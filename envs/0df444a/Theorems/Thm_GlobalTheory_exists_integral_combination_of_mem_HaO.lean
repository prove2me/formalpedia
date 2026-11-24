-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_combination_of_mem_HaO
-- name    : GlobalTheory.exists_integral_combination_of_mem_HaO
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:33:58.7303+00:00
-- url     : https://prove2.me/theorems/ee5f6ce8-04a3-45b5-860d-9b6f7fc1d835
-- title:
--   Global Theory: exists integral combination of mem Ha O
-- statement:
--   The Global Theory construction uses the exists integral combination of mem Ha O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralCombinationOfMemHaO.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsIntegralCombinationOfMemHaO.lean#L10-L41

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralBasisLinearCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemHHaOfCoeffFunctional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCombinationOfMemHaO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory

theorem GlobalTheory.exists_integral_combination_of_mem_HaO :
    ∀ (T : Type) (r : T → ℕ) (n : ℕ) (V K C : Type) [CommRing V] [IsDomain V] [IsPrincipalIdealRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field C] (e : K →+* C) (R : Subring C), (∀ x : V, e (algebraMap V K x) ∈ R) → ∀ (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) C), P ∈ HaO r n C R cc isX a → ∃ (s : ℕ) (c : Fin s → C) (Q : Fin s → MvPolynomial (Letter T r n) K), (∀ j, c j ∈ R) ∧ (∀ j, Q j ∈ HaO r n K (algebraMap V K).range cc isX a) ∧ P = ∑ j, MvPolynomial.C (c j) * MvPolynomial.map e (Q j) := by sorry
