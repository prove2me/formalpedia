-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GroupIndex_RelProd_relIndex_prod_eq_mul
-- name    : GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_eq_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:45:09.054343+00:00
-- url     : https://prove2.me/theorems/cfd75620-c450-4cbb-bd74-332db0ababf5
-- title:
--   Rel Prod: rel Index prod eq mul
-- statement:
--   The Rel Prod construction uses the rel Index prod eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdRelIndexNeZero.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdRelIndexNeZero.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GroupIndex GlobalTheory.CompanionTheory.GroupIndex.RelProd

theorem GlobalTheory.CompanionTheory.GroupIndex.RelProd.relIndex_prod_eq_mul {G₁ G₂ : Type} [Group G₁] [Group G₂]
    (I₁ K₁ : Subgroup G₁) (I₂ K₂ : Subgroup G₂) :
    (I₁.prod I₂).relIndex (K₁.prod K₂) = I₁.relIndex K₁ * I₂.relIndex K₂ := by sorry
