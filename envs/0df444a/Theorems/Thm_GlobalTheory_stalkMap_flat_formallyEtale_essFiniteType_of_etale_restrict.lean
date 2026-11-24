-- Prove2me | Theorems.Thm_GlobalTheory_stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict
-- name    : GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:29.719344+00:00
-- url     : https://prove2.me/theorems/2b5e0cc8-1ac4-49a9-8d3a-6383567a1b5e
-- title:
--   Global Theory: stalk Map flat formally Etale ess Finite Type of etale restrict
-- statement:
--   The Global Theory construction uses the stalk Map flat formally Etale ess Finite Type of etale restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L42-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes.lean#L42-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory
universe u

theorem GlobalTheory.stalkMap_flat_formallyEtale_essFiniteType_of_etale_restrict :
    ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U,
      (f.stalkMap y).hom.Flat ∧ (f.stalkMap y).hom.FormallyEtale ∧
        (f.stalkMap y).hom.EssFiniteType := by sorry
