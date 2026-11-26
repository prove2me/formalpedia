-- Prove2me | Theorems.Thm_NisanRonen_Rounding_boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances
-- name    : NisanRonen.Rounding.boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T07:16:04.263558+00:00
-- url     : https://prove2.me/theorems/ff2ddd74-f411-5989-b6d9-cabbf926820a
-- title:
--   Report certificates for the remaining cases with more jobs than machines
-- statement:
--   For each ε>0 and a>0, choose a single positive grid step δ<a with 2δ≤εa. For every b>a and every instance with at least two machines and more jobs than machines, prove report certificates for the bounded load dynamic program at the (1+ε) comparator bound when some assigned comparator entry is overreported after rounding and no admissible grid threshold satisfies the reserved-capacity lemma. This is the remaining case after equal counts, spare machines, and the two independent sufficient criteria.
-- source:
--   Nisan and Ronen (2001), Algorithmic Mechanism Design, §5.6, Theorem 5.9, https://doi.org/10.1006/game.1999.0790. Remaining report-certificate obligation for the colexicographic dynamic program.

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Definitions.Def_NisanRonen_Rounding_boundedLoadDP

namespace NisanRonen.Rounding

theorem boundedLoadDP_report_certificates_for_remaining_oversubscribed_instances :
    ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 < a → ∃ δ : ℝ,
      0 < δ ∧ δ < a ∧ 2 * δ ≤ ε * a ∧
      ∀ b : ℝ, a < b → ∀ (n : ℕ) [NeZero n], 2 ≤ n → ∀ k : ℕ, n < k →
        let f := boundedLoadDP (n := n) (⌈b / δ⌉.toNat)
        ∀ t d : Fin n → Fin k → ℝ,
          (∀ l j, a ≤ t l j ∧ t l j ≤ b) →
          (∀ l j, a ≤ d l j ∧ d l j ≤ b) →
          (∀ i, DeclarationOptimal f δ a b i (t i) (d i)) →
          ∀ y : Fin k → Fin n,
            (∃ j, roundUp δ (t (y j) j) < roundUp δ (d (y j) j)) →
            (¬ ∃ (M : ℝ) (c : ℕ), a ≤ M ∧ M ≤ b ∧ roundUp δ M = M ∧
              k - 1 ≤ (n - 2) * c ∧ (c : ℝ) * roundUp δ a < M ∧
              roundedMakespan δ y (corrStar y t) < M ∧
              M ≤ (1 + ε) * makespan y (corrStar y t)) →
            HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by sorry

end NisanRonen.Rounding
