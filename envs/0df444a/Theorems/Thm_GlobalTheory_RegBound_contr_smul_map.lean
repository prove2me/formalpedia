-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_contr_smul_map
-- name    : GlobalTheory.RegBound.contr_smul_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:20.248526+00:00
-- url     : https://prove2.me/theorems/0de47395-bc58-41e5-a5db-7c474ec30c30
-- title:
--   Reg Bound: contr smul map
-- statement:
--   The Reg Bound construction uses the contr smul map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L435-L439
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L435-L439

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
variable {L : Type} [Field L] [Algebra K L]

theorem GlobalTheory.RegBound.contr_smul_map (φ : L →ₗ[K] K) (c : L) (F : MvPolynomial σ K) :
    contr φ (c • map (algebraMap K L) F) = φ c • F := by sorry
