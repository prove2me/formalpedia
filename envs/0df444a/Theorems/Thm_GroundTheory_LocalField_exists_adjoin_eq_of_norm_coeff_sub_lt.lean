-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_adjoin_eq_of_norm_coeff_sub_lt
-- name    : GroundTheory.LocalField.exists_adjoin_eq_of_norm_coeff_sub_lt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:25.529567+00:00
-- url     : https://prove2.me/theorems/99900a01-a0ed-5141-ad03-b9e532d520f1
-- title:
--   Local Field: exists adjoin eq of norm coeff sub lt
-- statement:
--   The Local Field construction uses the exists adjoin eq of norm coeff sub lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L56-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExtensionsOfDegree.lean#L56-L159

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {L : Type*} [NontriviallyNormedField L]
variable [CompleteSpace L] [IsUltrametricDist L]

theorem GroundTheory.LocalField.exists_adjoin_eq_of_norm_coeff_sub_lt (f : L[X]) (hm : f.Monic) (hirr : Irreducible f)
    (hsep : f.Separable) (Ω' : Type*) [Field Ω'] [Algebra L Ω'] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : L[X], g.Monic → g.natDegree = f.natDegree → (∀ i, ‖g.coeff i‖ ≤ 1) →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → ∀ β : Ω', aeval β g = 0 →
        ∃ α : Ω', aeval α f = 0 ∧ L⟮α⟯ = L⟮β⟯ := by sorry
