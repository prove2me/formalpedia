-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_4_2
-- name    : GaussPart.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:06:37.333447+00:00
-- url     : https://prove2.me/theorems/b3a67764-98d7-4981-9907-a830e8e887a0
-- title:
--   Theorem 4.2 — agnostic QPTAS: error $(1+c)\mathrm{opt}+\epsilon$ under Gaussian-smooth marginals
-- statement:
--   **Setting.** Let $\mathcal F$ be an $(\ell,K)$-well-behaved class of Boolean $K$-MIMs on $\mathbb R^d$ (closed under affine restrictions, Gaussian $L_1$ sandwiching of degree $\ell$, finite Gaussian surface area $\Gamma(\mathcal F)$). Let $q\ge1$, $\sigma\in(0,1]$, $c,\epsilon\in(0,1/2)$, and let $D$ be a distribution on $\mathbb R^d\times\{\pm1\}$ whose x-marginal $D_x$ is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$; the labels are arbitrary. Write $\ell_c=\ell(c'c)$.
--
--   **Theorem.** There are universal constants $c'>0$ and $C$ such that for every such class there is an algorithm that, given $q,c,\epsilon,\sigma$, draws at most
--   $$
--   n=d^{C\ell_c}\exp\Bigl((qK\ell_c)^{C\ell_c}\log^{C\ell_c}\!\Bigl(\frac{2}{c\sigma\epsilon}\Bigr)\log\bigl(2+\Gamma(\mathcal F)\bigr)\Bigr)
--   $$
--   samples from $D$, runs in time $Cn^C$, and with probability at least $2/3$ outputs $h:\mathbb R^d\to\{\pm1\}$ with
--   $$
--   \mathrm{err}_D(h)\le(1+c)\,\mathrm{opt}_D(\mathcal F)+\epsilon .
--   $$
--
--   The exponent of $d$ depends on the approximation factor $c$ through the Gaussian sandwiching degree, but not on the excess error $\epsilon$.
--
--   **Formalization Note** The learner is a program of the published sampling RAM (arithmetic instructions only), the same as in the published Theorem 3.1; labeled samples are points of $\mathbb R^{d+1}$, bounds hold on every sample stream, and the program receives $K,\ell_c,\Gamma(\mathcal F)$ as inputs.
--
--   Differences from the source:
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·); ℓ_c = ℓ(c′c) for a sufficiently small universal c′ → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given q, c, ϵ, σ and the class numbers K, ℓ_c, Γ(F) in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 4.2, p.36 (PDF p.38); informal version Theorem 1.6, p.3

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_WellBehaved

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem 4.2** (Agnostic QPTAS under Smoothness Relative to a Gaussian).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 4.2, p.36 (PDF p.38);
informal version Theorem 1.6, p.3.

"Fix q ≥ 1, c, ϵ ∈ (0, 1/2), and σ ∈ (0, 1]. Let F ⊆ {ℝ^d → {±1}} be an (ℓ, K)-well-behaved MIM
class. Let D be a distribution over ℝ^d × {±1} whose x-marginal D_x is (q, σ)-smooth with respect to
N(0, I_d). Let ℓ_c = ℓ(c′c) for a sufficiently small universal constant c′. There exists an algorithm
that draws n = d^{O(ℓ_c)} exp((qKℓ_c)^{O(ℓ_c)} log^{O(ℓ_c)}(2/(cσϵ)) log(2 + Γ(F))) samples from D,
runs in poly(n) time, and, with probability at least 2/3, outputs a hypothesis h : ℝ^d → {±1} such
that err_D(h) ≤ (1 + c)opt_D(F) + ϵ."

**Formalization Note.**
* `c′` and one natural number `C` for every `O(·)` and for `poly(n) = C·n^C` are chosen first. The
  learner `P` and its evaluator `E` are programs of the published `GaussMixHH` machine restricted by
  `ArithmeticOnly`; they may depend on the class `F` (hence on `d`), and they are uniform in
  `q, c, ϵ, σ` and `D`. The memory holds `q, c, ϵ, σ, K, ℓ_c, Γ(F)` (the class numbers `K, ℓ_c, Γ(F)`
  cannot be computed from the class by a finite program).
* Labeled samples are points `(x, y)` of `ℝ^{d+1}` (`labeledEnc`); the bounds hold on every sample
  stream; success is a measurable set of streams of probability `≥ 2/3`. The hypothesis is the
  function `hyp E d (C n^C) s` computed from the final state within work `C n^C`.
* `d ≥ 1`. -/
theorem theorem_4_2 :
    ∃ c' : ℝ, 0 < c' ∧ ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ (ℓ : ℝ → ℕ) (K : ℕ) (F : Set (Vec d → ℝ)), IsWellBehaved ℓ K F →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q c ε σ : ℝ), 1 ≤ q → 0 < c → c < 1 / 2 → 0 < ε → ε < 1 / 2 → 0 < σ → σ ≤ 1 →
    ∀ (D : Measure (Vec d × ℝ)), IsLabeledLaw D →
      IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
      let ℓc : ℕ := ℓ (c' * c)
      let Γ : ℝ := (gsaClass F).toReal
      let n : ℝ := (d : ℝ) ^ (C * ℓc) *
        Real.exp ((q * K * ℓc) ^ (C * ℓc) * Real.log (2 / (c * σ * ε)) ^ (C * ℓc) *
          Real.log (2 + Γ))
      let inp : List ℝ := [q, c, ε, σ, (K : ℝ), (ℓc : ℝ), Γ]
      RunsWithin P (d + 1) inp n (C * n ^ C) ∧
      SucceedsWith P (d + 1) inp (labeledStream D) (2 / 3) (fun s =>
        err D (hyp E d (C * n ^ C) s) ≤ ENNReal.ofReal (1 + c) * opt D F + ENNReal.ofReal ε) := by sorry

end Supplement

end GaussPart
