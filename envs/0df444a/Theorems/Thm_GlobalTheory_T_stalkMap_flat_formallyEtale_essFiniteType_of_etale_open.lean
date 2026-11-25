-- Prove2me | Theorems.Thm_GlobalTheory_T_stalkMap_flat_formallyEtale_essFiniteType_of_etale_open
-- name    : GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:39:09.839347+00:00
-- url     : https://prove2.me/theorems/4c85f9a8-579a-5318-a441-58a25fc6a6e7
-- title:
--   T: stalk Map flat formally Etale ess Finite Type of etale open
-- statement:
--   The T construction uses the stalk Map flat formally Etale ess Finite Type of etale open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧ (f.stalkMap y).hom.EssFiniteType := by sorry
