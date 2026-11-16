-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_F_2
-- name    : GaussPart.Supplement.theorem_F_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:15:26.886413+00:00
-- url     : https://prove2.me/theorems/d2c2d37b-6fe8-46d3-bcb9-3d1be8049b67
-- title:
--   Theorem F.2 — testable agnostic learning of MIMs to error $(1+c)\mathrm{opt}+\epsilon$
-- statement:
--   **Setting.** Let $\mathcal F$ be an $(\ell,K,A,\Lambda)$-testable well-behaved class of Boolean $K$-MIMs on $\mathbb R^d$ for every $\Lambda\ge1$ (Definition F.1). Fix $q\ge1$, $\sigma\in(0,1]$ and $c,\epsilon\in(0,1/2)$, and let $\ell_c=\ell(c/C)$ for a sufficiently large universal constant $C$. Let $\mathcal D_{q,\sigma}$ be the distributions on $\mathbb R^d$ that are $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$.
--
--   **Theorem.** There is an algorithm that, given samples from any distribution $D$ on $\mathbb R^d\times\{\pm1\}$, testably learns $\mathcal F$ under $\mathcal D_{q,\sigma}$ to error $(1+c)\mathrm{opt}_D(\mathcal F)+\epsilon$ with probability at least $99\%$, using
--   $$
--   N=d^{C\ell_c}\exp\Bigl((qK\ell_c)^{C\ell_c}\log^{C\ell_c}\!\Bigl(\frac{2}{c\sigma\epsilon}\Bigr)\log(2+A)\Bigr)
--   $$
--   samples and time $CN^C$. That is: for every $D$, the probability that it accepts with a hypothesis of error above $(1+c)\mathrm{opt}_D(\mathcal F)+\epsilon$ is at most $1/100$; and if $D_x\in\mathcal D_{q,\sigma}$ it accepts with probability at least $99/100$.
--
--   **Formalization Note** One constant $C$ serves $\ell_c$, every $O(\cdot)$ and the polynomial; the program receives $q,\sigma,c,\epsilon,K,\ell_c,A$.
--
--   Differences from the source:
--   - encoding: testably learns F under D_{q,σ} with probability 1 − δ (Definition A.5) → soundness: for every labeled D, a measurable set of streams of probability ≥ 1 − δ on which acceptance implies the error bound; completeness: if D_x is (q, σ)-smooth, acceptance with probability ≥ 1 − δ; accept means final output register 1; reason: Pr[accept ∧ bad] ≤ δ is the same as a success set of probability ≥ 1 − δ for 'accept → good'
--   - reading: an (ℓ, K, A, Λ)-testable well-behaved class for every Λ ≥ 1 (Definition F.1) → IsTestableWellBehaved ℓ K A Λ F for all Λ ≥ 1 with ℓ, K, A fixed; one common subspace per cell; members Borel measurable; reason: the page attaches the common subspace to the pair of polynomials of a cell; Boolean functions are measurable (Definition A.1)
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·); ℓ_c = ℓ(c/C) for a sufficiently large universal C → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given q, σ, c, ϵ and the class numbers K, ℓ_c, A in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem F.2, p.79 (PDF p.81); Definition A.5, p.70; Definition F.1, p.79

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_ArithmeticOnly
import Definitions.Def_GaussPart_Supplement_Learner
import Definitions.Def_GaussPart_Supplement_LabeledLaw
import Definitions.Def_GaussPart_Supplement_TestableWellBehaved

open MeasureTheory ProbabilityTheory

namespace GaussPart

namespace Supplement

/-- **Theorem F.2** (Testable agnostic learning of MIMs).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem F.2, p.79 (PDF p.81);
Definition A.5, p.70 (PDF p.72); Definition F.1, p.79.

"Let F be an (ℓ, K, A, Λ)-testable well-behaved class for every Λ ≥ 1. Fix q ≥ 1, σ ∈ (0, 1], and
c, ϵ ∈ (0, 1/2). For a sufficiently large universal constant C, let ℓ_c = ℓ(c/C). There is an
algorithm that, given samples from any distribution D on ℝ^d × {±1}, testably learns F under D_{q,σ}
to error (1 + c)opt_D(F) + ϵ with probability at least 99%, using
N = d^{O(ℓ_c)} exp((qKℓ_c)^{O(ℓ_c)} log^{O(ℓ_c)}(2/(cσϵ)) log(2 + A)) samples from D and running in
time poly(N)."

**Formalization Note.**
* One natural number `C` serves as the constant of `ℓ_c = ℓ(c/C)`, of every `O(·)` and of
  `poly(N) = C N^C` (each is monotone in `C`, so `∃ C` is "sufficiently large `C`"). The class
  parameters `ℓ, K, A` are fixed for all `Λ ≥ 1`. The program may depend on the class and receives
  `q, σ, c, ϵ, K, ℓ_c, A` (Algorithm 6, p.80, takes the class parameters as input).
* Testable learning with probability `99%` (Definition A.5 with `δ = 1/100`): **soundness** for every
  `D` on `ℝᵈ × {±1}`: with probability `≥ 99/100`, if the learner accepts (`Accepts`, final
  `r[0] = 1`) its hypothesis has `err_D(h) ≤ (1 + c)opt_D(F) + ϵ`; **completeness**: if `D_x` is
  `(q, σ)`-smooth with respect to `N(0, I_d)` (`D_x ∈ D_{q,σ}`), it accepts with probability
  `≥ 99/100`.
* Labeled samples, bounds on every stream, success on a measurable set of streams and the evaluated
  hypothesis are as in `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_F_2 :
    ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ (ℓ : ℝ → ℕ) (K : ℕ) (A : ℝ) (F : Set (Vec d → ℝ)),
      (∀ Λ : ℝ, 1 ≤ Λ → IsTestableWellBehaved ℓ K A Λ F) →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q σ c ε : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < c → c < 1 / 2 → 0 < ε → ε < 1 / 2 →
      let ℓc : ℕ := ℓ (c / C)
      let N : ℝ := (d : ℝ) ^ (C * ℓc) *
        Real.exp ((q * K * ℓc) ^ (C * ℓc) * Real.log (2 / (c * σ * ε)) ^ (C * ℓc) *
          Real.log (2 + A))
      let inp : List ℝ := [q, σ, c, ε, (K : ℝ), (ℓc : ℝ), A]
      RunsWithin P (d + 1) inp N (C * N ^ C) ∧
      ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
        SucceedsWith P (d + 1) inp (labeledStream D) (99 / 100) (fun s =>
          Accepts s →
            err D (hyp E d (C * N ^ C) s) ≤ ENNReal.ofReal (1 + c) * opt D F + ENNReal.ofReal ε) ∧
        (IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith P (d + 1) inp (labeledStream D) (99 / 100) Accepts) := by sorry

end Supplement

end GaussPart
