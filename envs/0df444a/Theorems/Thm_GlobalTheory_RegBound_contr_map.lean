-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_contr_map
-- name    : GlobalTheory.RegBound.contr_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:18:25.673798+00:00
-- url     : https://prove2.me/theorems/6d9a3702-3d6a-4b27-a17a-ba671e12bec9
-- title:
--   Reg Bound: contr map
-- statement:
--   The Reg Bound construction uses the contr map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L441-L443
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L441-L443

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

theorem GlobalTheory.RegBound.contr_map (φ : L →ₗ[K] K) (F : MvPolynomial σ K) :
    contr φ (map (algebraMap K L) F) = φ 1 • F := by sorry
