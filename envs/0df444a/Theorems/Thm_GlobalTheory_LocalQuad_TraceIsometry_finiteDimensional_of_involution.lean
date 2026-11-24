-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_finiteDimensional_of_involution
-- name    : GlobalTheory.LocalQuad.TraceIsometry.finiteDimensional_of_involution
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:14:16.902021+00:00
-- url     : https://prove2.me/theorems/134b74a4-39dd-4198-8119-06bf40a02952
-- title:
--   Trace Isometry: finite Dimensional of involution
-- statement:
--   The Trace Isometry construction uses the finite Dimensional of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L13-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsCongrIffTraceFormsIsometric.lean#L13-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}

theorem GlobalTheory.LocalQuad.TraceIsometry.finiteDimensional_of_involution (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t) : FiniteDimensional F E := by sorry
