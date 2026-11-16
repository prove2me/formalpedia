-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_5_3
-- name    : GaussPart.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:08:20.138241+00:00
-- url     : https://prove2.me/theorems/8333a7a2-52a4-4280-b798-60e97a92b27d
-- title:
--   Theorem 5.3 — PUI learning with a Gaussian reference in $d^{m^*}$ samples
-- statement:
--   **Setting.** Let $\mathcal F$ be a class of Boolean functions on $\mathbb R^d$ that is closed under affine restrictions and has finite Gaussian surface area $\Gamma(\mathcal F)$. The reference distribution is $D=\mathcal N(0,I_d)$; $D^*$ is $(q,\sigma)$-smooth with respect to $D$ ($q\ge1$, $\sigma\in(0,1]$). The target $f\in\mathcal F$ is unknown, $p_+>0$ satisfies $D^*(f=1)\ge p_+$, and $D^*_+=D^*\mid\{f=1\}$. Let $\epsilon,\Delta\in(0,1/2)$ and
--   $$
--   k=m^*\bigl(c\epsilon,\ \Delta,\ c'\epsilon\sigma p_+/q,\ 2q\bigr)<\infty,
--   $$
--   where $m^*$ is the Gaussian PUI learning exponent (Definition 5.2) and $c,c'>0$ are small universal constants.
--
--   **Theorem.** There is a PUI learning algorithm that, given $\epsilon,\sigma,p_+,\Delta,q$ and
--   $$
--   d^{k}\exp\Bigl((qk)^{Ck}\log^{Ck}\!\Bigl(\frac{2}{\sigma\epsilon p_+}\Bigr)\log\bigl(2+\Gamma(\mathcal F)\bigr)/\Delta^{C}\Bigr)
--   $$
--   samples from $D^*_+$, runs in time polynomial in this number and with probability at least $2/3$ outputs $h$ with
--   $$
--   \Pr_{x\sim D^*}[h(x)\neq f(x)]\le\epsilon .
--   $$
--
--   Together with the SQ lower bound (Theorem 5.4) this shows that the moment-matching exponent $m^*$ qualitatively governs PUI learning with a Gaussian reference.
--
--   **Formalization Note** The learner sees i.i.d. samples of $D^*_+$ only, and receives $k$ and $\Gamma(\mathcal F)$ as inputs; the sample count has the bare factor $d^k$.
--
--   Differences from the source:
--   - reading: bounded Gaussian surface area Γ(F) ≤ ∞ (items (1) and (3) of Definition 4.1) → Γ(F) < ∞; reason: the parenthesis refers to item (3), which requires Γ(F) < ∞; '≤ ∞' would be vacuous
--   - reading: a class of functions with Gaussian surface area → members are Borel measurable ±1-valued functions; reason: Definition A.1 defines Γ(f) for Borel measurable Boolean functions
--   - encoding: assume k < ∞ → m∗(cϵ, Δ, c′ϵσp₊/q, 2q) = k for a natural number k; reason: m∗ takes values in ℕ ∪ {∞}
--   - encoding: p₊ > 0 with D∗(f = 1) ≥ p₊ → 0 < p₊ ≤ 1 as an input, the target condition D∗(f = 1) ≥ p₊ in the success clause; reason: the complexity clause is stated for every input; p₊ > 1 admits no target
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·); sufficiently small universal c, c′ → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given ϵ, σ, p₊, Δ, q and the class numbers k, Γ(F) in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 5.3, p.44 (PDF p.46); informal version Theorem 1.8 (i), p.5; Definition 5.2, p.44

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_BoolFn
import Definitions.Def_GaussPart_Supplement_SurfaceArea
import Definitions.Def_GaussPart_Supplement_PUIExponent

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 5.3** (PUI Learning with Gaussian References).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 5.3, p.44 (PDF p.46);
informal version Theorem 1.8 (i), p.5.

"Let F be a class of functions that is closed under affine restrictions and has bounded Gaussian
surface area Γ(F) ≤ ∞ (satisfies items (1) and (3) of Definition 4.1), let the reference distribution
be the standard Gaussian D = N(0, I_d), and let D∗ be a target distribution that is (q, σ)-smooth
with respect to D, q ≥ 1 and σ ∈ (0, 1]. Let f ∈ F be an unknown function, let p+ > 0 satisfy
D∗(f = 1) ≥ p+, and set D∗_+ = D∗ | f(x) = 1. Let ϵ, ∆ ∈ (0, 1/2) and set
k = m∗(cϵ, ∆, c′ϵσp+/q, 2q) for sufficiently small universal constants c, c′ > 0, and assume k < ∞.
There exists a PUI learning algorithm that, given ϵ, σ, p+, ∆, q and
d^k exp((qk)^{O(k)} log^{O(k)}(2/(σϵp+)) log(2 + Γ(F))/∆^{O(1)}) samples from D∗_+, runs in time
polynomial in its sample complexity and with probability at least 2/3 outputs a hypothesis h such
that Pr_{x∼D∗}[h(x) ≠ f(x)] ≤ ϵ."

**Formalization Note.**
* "Γ(F) ≤ ∞" is read as item (3) of Definition 4.1, `Γ(F) < ∞`. Members of `F` are Borel
  measurable `±1`-valued functions (`IsBoolFn`), as Definition A.1 requires for `Γ`.
* `c, c′` and one natural number `C` for every `O(·)` and `poly` are chosen first; the program may
  depend on `F` and is uniform in `ϵ, σ, p₊, ∆, q`, the target and `D∗`. Its memory holds
  `ϵ, σ, p₊, ∆, q` and the class numbers `k` and `Γ(F)`. `p₊ ≤ 1`: a lower bound on `D∗(f = 1)`
  larger than `1` admits no target, and the complexity clause is stated for every input. `k < ∞` is `m∗(…) = k` for a natural `k`
  (`mStar`, Definition 5.2). The sample count is `d^k · exp(…)` with the bare `d^k`.
* The learner reads i.i.d. samples of `D∗₊ = cond D∗ {f = 1}` only; the error is under `D∗`.
* Bounds on every stream, success on a measurable set of streams, the evaluated hypothesis: as in
  `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_5_3 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ F : Set (Vec d → ℝ), (∀ f ∈ F, IsBoolFn f) →
      ClosedUnderAffineRestr F → gsaClass F < ⊤ →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q σ ε Δ pPos : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < ε → ε < 1 / 2 → 0 < Δ → Δ < 1 / 2 →
      0 < pPos → pPos ≤ 1 →
    ∀ k : ℕ, mStar F (c * ε) Δ (c' * ε * σ * pPos / q) (2 * q) = (k : ℕ∞) →
      let Γ : ℝ := (gsaClass F).toReal
      let n : ℝ := (d : ℝ) ^ k *
        Real.exp ((q * k) ^ (C * k) * Real.log (2 / (σ * ε * pPos)) ^ (C * k) *
          Real.log (2 + Γ) / Δ ^ C)
      let inp : List ℝ := [ε, σ, pPos, Δ, q, (k : ℝ), Γ]
      RunsWithin P d inp n (C * n ^ C) ∧
      ∀ f ∈ F, ∀ Ds : Measure (Vec d), IsProbabilityMeasure Ds →
        IsSmooth (stdGaussian (Vec d)) Ds q σ → ENNReal.ofReal pPos ≤ Ds {x | f x = 1} →
        SucceedsWith P d inp (Measure.infinitePi fun _ : ℕ => cond Ds {x | f x = 1}) (2 / 3)
          (fun s => Ds {x | hyp E d (C * n ^ C) s x ≠ f x} ≤ ENNReal.ofReal ε) := by sorry

end Supplement

end GaussPart
