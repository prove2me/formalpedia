-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PartialZeta_im_ne_zero
-- name    : GlobalTheory.Mem.PartialZeta.im_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:23:03.895631+00:00
-- url     : https://prove2.me/theorems/4c81fdbb-5ba6-4765-9b41-15e99bc55071
-- title:
--   Partial Zeta: im ne zero
-- statement:
--   The Partial Zeta construction uses the im ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L47-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L47-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.PartialZeta.im_ne_zero [IsTotallyComplex K] (φ : K →+* ℂ) (b : Module.Basis (Fin 2) ℤ (𝓞 K)) :
    (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ≠ 0 := by sorry
