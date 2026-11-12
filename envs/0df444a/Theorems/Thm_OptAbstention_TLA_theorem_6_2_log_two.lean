-- Prove2me | Theorems.Thm_OptAbstention_TLA_theorem_6_2_log_two
-- name    : OptAbstention.TLA.theorem_6_2_log_two
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:19:36.408242+00:00
-- url     : https://prove2.me/theorems/fc8e2209-3058-4341-a4dc-971c30005737
-- title:
--   Theorem 6.2 with log(2/δ) (corrected: the printed log(1/δ) bound vanishes as δ → 1)
-- statement:
--   **Source:** Theorem 6.2 ($L_1$ polynomial regression) with sample complexity and runtime $\mathrm{poly}((d+1)^\ell, 1/\varepsilon) \cdot \log(1/\delta)$.
--
--   **Variant:** the same statement with $\log(2/\delta)$ in place of $\log(1/\delta)$ in both bounds.
--
--   **Difference:** the two differ only for $\delta$ near $1$, where the printed bound falls below one step.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 13, Theorem 6.2 (corrected)

import Mathlib
import Definitions.Def_OptAbstention_TLA_Sandwiching
import Definitions.Def_OptAbstention_TLA_Empirical
import Definitions.Def_OptAbstention_TLA_Machine
import Definitions.Def_OptAbstention_TLA_SelectorIO
open MeasureTheory

namespace OptAbstention.TLA

/-- Theorem 6.2 (implicit in KKMS08), p. 13, with `log(2/δ)` in place of the printed `log(1/δ)`: for every `d, ℓ, ε, δ`
one program (the degree-`ℓ` L1 polynomial regression algorithm) that, on every run, draws at most
and runs at most `C·((d+1)^ℓ/ε)^k·log(1/δ)` samples and steps and outputs a degree-`ℓ` polynomial
threshold function, and that for every `X`, every labeled distribution `D̄` and every class `C`
whose members are `ε`-approximated in `L1(D)` by degree-`ℓ` polynomials, has error at most
`opt + ε` except on a set of measure at most `δ`. -/
theorem theorem_6_2_log_two : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (d ℓ : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ P : Program,
    Admissible P ∧
    (∀ (ξ : ExStream d) (ν : Tape),
      HaltsWithin P d ξ ν emptyInit
        (C * ((((d : ℝ) + 1) ^ ℓ) / ε) ^ k * Real.log (2 / δ))
        (C * ((((d : ℝ) + 1) ^ ℓ) / ε) ^ k * Real.log (2 / δ))) ∧
    ∀ (X : Set (Pt d)) (Dbar : Measure (X × Bool)) [IsProbabilityMeasure Dbar]
      (Cl : Set (X → ℝ)), IsConceptClass X Cl →
      (∀ f ∈ Cl, ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ℓ ∧
        ∫⁻ x, ENNReal.ofReal |peval p (x : Pt d) - f x| ∂(Dbar.map Prod.fst) ≤
          ENNReal.ofReal ε) →
      streamLaw Dbar
        {ω | ¬ ∃ St, finalState P d ω.1 ω.2 emptyInit = some St ∧ ValidPTF d ℓ St.cfg.mem ∧
          trainErr Dbar (fun x : X => ptfClassifier d St.cfg.mem (x : Pt d)) ≤
            optTrain Dbar Cl + ENNReal.ofReal ε}
        ≤ ENNReal.ofReal δ := by sorry

end OptAbstention.TLA
