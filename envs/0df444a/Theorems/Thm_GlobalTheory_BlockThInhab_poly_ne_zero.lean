-- Prove2me | Theorems.Thm_GlobalTheory_BlockThInhab_poly_ne_zero
-- name    : GlobalTheory.BlockThInhab.poly_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:58:33.433971+00:00
-- url     : https://prove2.me/theorems/05f5c5c9-db37-44a6-af3d-b8c637f88316
-- title:
--   Block Th Inhab: poly ne zero
-- statement:
--   The Block Th Inhab construction uses the poly ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NotIsBlockProdZero.lean#L14-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NotIsBlockProdZero.lean#L14-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsBlockProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NotIsBlockProdZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BlockThInhab
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.BlockTh
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (n : ℕ)

theorem GlobalTheory.BlockThInhab.poly_ne_zero (K : Type) [Field K] (B : Bk Dw n) : B.poly K ≠ 0 := by sorry
