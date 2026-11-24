-- Prove2me | Theorems.Thm_GlobalTheory_GenEigenFinOrbit_foldr_eq_prod
-- name    : GlobalTheory.GenEigenFinOrbit.foldr_eq_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:58.581812+00:00
-- url     : https://prove2.me/theorems/22d677fd-9ee1-45cb-a944-5daf6fa6f8fb
-- title:
--   Gen Eigen Fin Orbit: foldr eq prod
-- statement:
--   The Gen Eigen Fin Orbit construction uses the foldr eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSpanGenEigenOfFiniteDimensionalOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.GenEigenFinOrbit
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.GenEigenFinOrbit.foldr_eq_prod (χ : End ℂ V → ℂ) (zs : List (End ℂ V)) (v : V) :
    zs.foldr (fun z f => z f - χ z • f) v =
      (zs.map (fun z => z - algebraMap ℂ (End ℂ V) (χ z))).prod v := by sorry
