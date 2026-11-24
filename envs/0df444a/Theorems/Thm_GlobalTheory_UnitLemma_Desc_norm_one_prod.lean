-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_one_prod
-- name    : GlobalTheory.UnitLemma.Desc.norm_one_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:28:07.043838+00:00
-- url     : https://prove2.me/theorems/72119aee-105d-4817-a4a1-d58431f4e3a0
-- title:
--   Desc: norm one prod
-- statement:
--   The Desc construction uses the norm one prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUniformizerIdempotentFrameProd.lean#L18-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUniformizerIdempotentFrameProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc

theorem GlobalTheory.UnitLemma.Desc.norm_one_prod {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by sorry
