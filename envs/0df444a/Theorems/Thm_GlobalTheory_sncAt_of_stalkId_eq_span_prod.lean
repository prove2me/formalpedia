-- Prove2me | Theorems.Thm_GlobalTheory_sncAt_of_stalkId_eq_span_prod
-- name    : GlobalTheory.sncAt_of_stalkId_eq_span_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:04:13.188346+00:00
-- url     : https://prove2.me/theorems/e4812dde-90d1-433e-b2bd-b4936266a114
-- title:
--   Global Theory: snc At of stalk Id eq span prod
-- statement:
--   The Global Theory construction uses the snc At of stalk Id eq span prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SncAtOfStalkIdEqSpanProd.lean#L10-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SncAtOfStalkIdEqSpanProd.lean#L10-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SncAtOfStalkIdEqSpanProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R
open GlobalTheory

theorem GlobalTheory.sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by sorry
