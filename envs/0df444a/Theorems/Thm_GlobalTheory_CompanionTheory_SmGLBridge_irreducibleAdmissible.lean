-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmGLBridge_irreducibleAdmissible
-- name    : GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:33.994179+00:00
-- url     : https://prove2.me/theorems/3eea564e-b6b6-5402-a116-edbf3671aa62
-- title:
--   Sm GLBridge: irreducible Admissible
-- statement:
--   The Sm GLBridge construction uses the irreducible Admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L36-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L36-L87

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

theorem GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.SmGL.IrreducibleAdmissible k := by sorry
