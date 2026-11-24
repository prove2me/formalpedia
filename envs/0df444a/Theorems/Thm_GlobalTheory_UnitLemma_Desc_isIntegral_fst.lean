-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_isIntegral_fst
-- name    : GlobalTheory.UnitLemma.Desc.isIntegral_fst
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:27:31.068126+00:00
-- url     : https://prove2.me/theorems/1525baf0-1aa1-4289-a22d-947153e51021
-- title:
--   Desc: is Integral fst
-- statement:
--   The Desc construction uses the is Integral fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L40-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L40-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ProductLatticePositionsAndTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
variable {R A₁ A₂ : Type} [CommRing R] [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]

theorem GlobalTheory.UnitLemma.Desc.isIntegral_fst {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.1 := by sorry
