-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmGLBridge_glReindex_symm
-- name    : GlobalTheory.CompanionTheory.SmGLBridge.glReindex_symm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:56:49.31659+00:00
-- url     : https://prove2.me/theorems/81d03308-34c0-43ea-9d69-f7c64eec751a
-- title:
--   Sm GLBridge: gl Reindex symm
-- statement:
--   The Sm GLBridge construction uses the gl Reindex symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmGLBridge
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

theorem GlobalTheory.CompanionTheory.SmGLBridge.glReindex_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (g : GL b k) : (glReindex (k := k) e).symm g = glReindex e.symm g := by sorry
