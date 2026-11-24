-- Prove2me | Theorems.Thm_GlobalTheory_FibreHyp_preirreducibleSpace_congr
-- name    : GlobalTheory.FibreHyp.preirreducibleSpace_congr
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:24:36.985111+00:00
-- url     : https://prove2.me/theorems/b1d1b065-517a-49a0-b94f-1cb220777e65
-- title:
--   Fibre Hyp: preirreducible Space congr
-- statement:
--   The Fibre Hyp construction uses the preirreducible Space congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean#L166-L174

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceFibreHypersurfaceSpectrumIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.FibreHyp

theorem GlobalTheory.FibreHyp.preirreducibleSpace_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    PreirreducibleSpace X ↔ PreirreducibleSpace Y := by sorry
