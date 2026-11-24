-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_isIntegral_prod_iff
-- name    : GlobalTheory.UnitLemma.ProdCount.isIntegral_prod_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:41.528055+00:00
-- url     : https://prove2.me/theorems/1f9acd5d-6514-41b5-aeb9-45773f35bbaa
-- title:
--   Prod Count: is Integral prod iff
-- statement:
--   The Prod Count construction uses the is Integral prod iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L63-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]

theorem GlobalTheory.UnitLemma.ProdCount.isIntegral_prod_iff (t : A₁ × A₂) : IsIntegral O t ↔ IsIntegral O t.1 ∧ IsIntegral O t.2 := by sorry
