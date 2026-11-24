-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_isIntegral_snd
-- name    : GlobalTheory.UnitLemma.Desc.isIntegral_snd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:29:30.615292+00:00
-- url     : https://prove2.me/theorems/749b3f6b-2c34-4546-9912-7c6c5d0195bf
-- title:
--   Desc: is Integral snd
-- statement:
--   The Desc construction uses the is Integral snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L42-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ProductLatticePositionsAndTerms.lean#L42-L42

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

theorem GlobalTheory.UnitLemma.Desc.isIntegral_snd {x : A₁ × A₂} (hx : IsIntegral R x) : IsIntegral R x.2 := by sorry
