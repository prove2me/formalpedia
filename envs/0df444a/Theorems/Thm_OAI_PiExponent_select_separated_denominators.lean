-- Prove2me | Theorems.Thm_OAI_PiExponent_select_separated_denominators
-- name    : OAI.PiExponent.select_separated_denominators
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T07:53:54.881405+00:00
-- url     : https://prove2.me/theorems/2f0fed5f-dba5-43d7-9172-9dc496ab1bd9
-- title:
--   Finite selection of denominators meeting successive weight thresholds
-- statement:
--   If an arbitrary relation admits nonzero integer numerators and denominators at least two with unbounded logarithmic weights, select any prescribed finite number of such pairs. Each weight exceeds a common lower bound and a threshold depending only on previously selected weights. Finite recursive choice proves the assertion. For zero pairs both conclusions are vacuous; no positivity of the common lower bound or any monotonicity of the threshold function is needed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_DeterminantSetup

theorem OAI.PiExponent.select_separated_denominators
    (R : ℤ → ℕ → Prop)
    (hR : ∀ L : ℕ, ∃ (p : ℤ) (q : ℕ),
      2 ≤ q ∧ p ≠ 0 ∧ L ≤ Nat.ceil (Real.log (q : ℝ)) ∧ R p q)
    (m W : ℕ) (S : List ℕ → ℕ) :
    ∃ (p : Fin m → ℤ) (q : Fin m → ℕ),
      (∀ i : Fin m, 2 ≤ q i ∧ p i ≠ 0 ∧
        W ≤ Nat.ceil (Real.log (q i : ℝ)) ∧ R (p i) (q i)) ∧
      OAI.PiExponent.separatedWeights S
        (fun i : Fin m => Nat.ceil (Real.log (q i : ℝ))) := by sorry
