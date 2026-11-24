-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ProdCount_intUnits_prod
-- name    : GlobalTheory.UnitLemma.ProdCount.intUnits_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:38.796259+00:00
-- url     : https://prove2.me/theorems/e25f6ade-7ee7-489d-9546-4ebc7d344cfa
-- title:
--   Prod Count: int Units prod
-- statement:
--   The Prod Count construction uses the int Units prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountProdOfIdempotentSeparable.lean#L78-L85

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

theorem GlobalTheory.UnitLemma.ProdCount.intUnits_prod (t : (A₁ × A₂)ˣ) :
    t ∈ intUnits O (A₁ × A₂) ↔
      (MulEquiv.prodUnits t).1 ∈ intUnits O A₁ ∧ (MulEquiv.prodUnits t).2 ∈ intUnits O A₂ := by sorry
