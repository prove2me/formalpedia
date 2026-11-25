-- Prove2me | Theorems.Thm_GlobalTheory_T_sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing
-- name    : GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:27.244526+00:00
-- url     : https://prove2.me/theorems/c4f2ad71-da77-5626-a03c-a2e09b99c67f
-- title:
--   T: snc At of stalk Id eq span prod of is Regular Local Ring
-- statement:
--   The T construction uses the snc At of stalk Id eq span prod of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SncAtOfStalkIdEqSpanProdStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SncAtOfStalkIdEqSpanProdStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SncAtOfStalkIdEqSpanProd
import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SncAtOfStalkIdEqSpanProdStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y), IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)), FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by sorry
