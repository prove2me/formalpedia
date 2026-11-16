-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_F_3
-- name    : GaussPart.Supplement.theorem_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:15:52.622098+00:00
-- url     : https://prove2.me/theorems/3a3d7a91-c5bf-4be7-8850-9b96b65d8dbf
-- title:
--   Theorem F.3 — testable weak learner: error $\le 1/2-c/12$ with confidence $1-\beta$
-- statement:
--   **Setting.** Let $\mathcal F$ be an $(\ell,K,A,\Lambda)$-testable well-behaved class for every $\Lambda\ge1$. Fix $q\ge1$, $\sigma\in(0,1]$ and $c,\beta\in(0,1/2)$, and let $\ell_c=\ell(c/C)$ for a sufficiently large universal constant $C$.
--
--   **Theorem.** There is an algorithm that, given samples from any distribution $D$ on $\mathbb R^d\times\{\pm1\}$, uses
--   $$
--   n=d^{C\ell_c}\exp\Bigl((qK\ell_c)^{C\ell_c}\log^{C\ell_c}\!\Bigl(\frac{2}{c\sigma}\Bigr)\log(2+A)\Bigr)\log^{C}\!\Bigl(\frac2\beta\Bigr)
--   $$
--   samples and time $Cn^C$, and
--
--   1. (**soundness**) whenever $\mathrm{opt}_D(\mathcal F)\le1/(2(1+c))$, with probability at least $1-\beta$, if it accepts then its hypothesis has $\mathrm{err}_D(h)\le 1/2-c/12$;
--   2. (**completeness**) for every $D$ whose x-marginal is $(q,\sigma)$-smooth with respect to $\mathcal N(0,I_d)$, regardless of $\mathrm{opt}_D(\mathcal F)$, it accepts with probability at least $1-\beta$.
--
--   Boosting this testable weak learner gives Theorem F.2.
--
--   **Formalization Note** The program receives $q,\sigma,c,\beta,K,\ell_c,A$.
--
--   Differences from the source:
--   - encoding: testably learns F under D_{q,σ} with probability 1 − δ (Definition A.5) → soundness: for every labeled D, a measurable set of streams of probability ≥ 1 − δ on which acceptance implies the error bound; completeness: if D_x is (q, σ)-smooth, acceptance with probability ≥ 1 − δ; accept means final output register 1; reason: Pr[accept ∧ bad] ≤ δ is the same as a success set of probability ≥ 1 − δ for 'accept → good'
--   - reading: an (ℓ, K, A, Λ)-testable well-behaved class for every Λ ≥ 1 (Definition F.1) → IsTestableWellBehaved ℓ K A Λ F for all Λ ≥ 1 with ℓ, K, A fixed; one common subspace per cell; members Borel measurable; reason: the page attaches the common subspace to the pair of polynomials of a cell; Boolean functions are measurable (Definition A.1)
--   - encoding: there is an algorithm that draws n samples and runs in poly(n) time → one program of the published GaussMixHH sampling RAM restricted by ArithmeticOnly, with an evaluator program computing h within the same budget; sample count ≤ n and work ≤ C·n^C on every sample stream; success on a measurable set of streams; reason: the machine model of the base mission; the paper's algorithm and time bound read in it
--   - encoding: O(·), poly(·); ℓ_c = ℓ(c/C); log^{O(1)}(2/β) → one universal natural C (and the named constants) chosen before d and every parameter; reason: a universal constant is chosen before what it is uniform over; one constant may serve several O(·) since each bound is monotone in it
--   - encoding: the parameters fixed before 'there is an algorithm' → one program, chosen after the class, given q, σ, c, β and the class numbers K, ℓ_c, A in memory; reason: a finite program with rational literals cannot hard-code real parameters or class numbers; the program may depend on the class, never on the target or the distribution
--   - reading: ℝ^d → d ≥ 1; reason: the dimension is a positive integer; at d = 0 the bound d^{…} is 0
--   - encoding: a hypothesis h : ℝ^d → {±1} and Pr[h(x) ≠ y] → h(x) = 1 if the evaluator halts within the work budget with output 1, else −1; probabilities in [0, ∞] (outer measure when h is not shown measurable); reason: the output of a machine is a description; bounding the error by an outer measure only strengthens the claim
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem F.3, p.80 (PDF p.82); Definition A.5, p.70; Definition F.1, p.79

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

/-- **Theorem F.3** (Testable weak learner).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem F.3, p.80 (PDF p.82);
Definition A.5, p.70 (PDF p.72); Definition F.1, p.79.

"Let F be an (ℓ, K, A, Λ)-testable well-behaved class for every Λ ≥ 1. Fix q ≥ 1, σ ∈ (0, 1], and
c, β ∈ (0, 1/2). For a sufficiently large universal constant C, let ℓ_c = ℓ(c/C). There is an
algorithm that, given samples from any distribution D on ℝ^d × {±1}, testably learns F under D_{q,σ}
with probability at least 1 − β, to error 1/2 − c/12 whenever opt_D(F) ≤ 1/(2(1 + c)). The algorithm
uses n = d^{O(ℓ_c)} exp((qKℓ_c)^{O(ℓ_c)} log^{O(ℓ_c)}(2/(cσ)) log(2 + A)) log^{O(1)}(2/β) samples from
D and runs in time poly(n). Its completeness guarantee holds for every D with D_x ∈ D_{q,σ}, regardless
of opt_D(F)."

**Formalization Note.**
* One natural number `C` serves as the constant of `ℓ_c = ℓ(c/C)`, of every `O(·)` and of
  `poly(n) = C n^C`. The class parameters `ℓ, K, A` are fixed for all `Λ ≥ 1`. The program may depend
  on the class and receives `q, σ, c, β, K, ℓ_c, A`.
* **Soundness** (only when `opt_D(F) ≤ 1/(2(1 + c))`): with probability `≥ 1 − β`, if the learner
  accepts, its hypothesis has `err_D(h) ≤ 1/2 − c/12`. **Completeness** (every `D` with `D_x`
  `(q, σ)`-smooth, whatever `opt_D(F)`): it accepts with probability `≥ 1 − β`.
* Labeled samples, bounds on every stream, success on a measurable set of streams and the evaluated
  hypothesis are as in `theorem_4_2`. `d ≥ 1`. -/
theorem theorem_F_3 :
    ∃ C : ℕ,
    ∀ (d : ℕ), 1 ≤ d → ∀ (ℓ : ℝ → ℕ) (K : ℕ) (A : ℝ) (F : Set (Vec d → ℝ)),
      (∀ Λ : ℝ, 1 ≤ Λ → IsTestableWellBehaved ℓ K A Λ F) →
    ∃ (P : GaussMixHH.Program) (_ : GaussMixHH.Admissible P) (_ : ArithmeticOnly P)
      (E : GaussMixHH.Program) (_ : GaussMixHH.Admissible E) (_ : ArithmeticOnly E),
    ∀ (q σ c β : ℝ), 1 ≤ q → 0 < σ → σ ≤ 1 → 0 < c → c < 1 / 2 → 0 < β → β < 1 / 2 →
      let ℓc : ℕ := ℓ (c / C)
      let n : ℝ := (d : ℝ) ^ (C * ℓc) *
        Real.exp ((q * K * ℓc) ^ (C * ℓc) * Real.log (2 / (c * σ)) ^ (C * ℓc) *
          Real.log (2 + A)) * Real.log (2 / β) ^ C
      let inp : List ℝ := [q, σ, c, β, (K : ℝ), (ℓc : ℝ), A]
      RunsWithin P (d + 1) inp n (C * n ^ C) ∧
      ∀ D : Measure (Vec d × ℝ), IsLabeledLaw D →
        (opt D F ≤ ENNReal.ofReal (1 / (2 * (1 + c))) →
          SucceedsWith P (d + 1) inp (labeledStream D) (ENNReal.ofReal (1 - β)) (fun s =>
            Accepts s → err D (hyp E d (C * n ^ C) s) ≤ ENNReal.ofReal (1 / 2 - c / 12))) ∧
        (IsSmooth (stdGaussian (Vec d)) (D.map Prod.fst) q σ →
          SucceedsWith P (d + 1) inp (labeledStream D) (ENNReal.ofReal (1 - β)) Accepts) := by sorry

end Supplement

end GaussPart
