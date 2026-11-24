-- Prove2me | Theorems.Thm_GlobalTheory_GenEigenFinOrbit_finrank_map_prod_le
-- name    : GlobalTheory.GenEigenFinOrbit.finrank_map_prod_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:56.814454+00:00
-- url     : https://prove2.me/theorems/7e495728-77b0-41f8-9554-c8a3d7a5a2ff
-- title:
--   Gen Eigen Fin Orbit: finrank map prod le
-- statement:
--   The Gen Eigen Fin Orbit construction uses the finrank map prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L43-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemSpanGenEigenOfFiniteDimensionalOrbit.lean#L43-L66

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
variable (G : Set (End ℂ V)) (N : Submodule ℂ V) (K : ℕ)
  (hcomm : ∀ a ∈ G, ∀ b ∈ G, a * b = b * a)
  (hst : ∀ g ∈ G, N.map g ≤ N) (hnil : ∀ g ∈ G, ∀ n ∈ N, (g ^ K) n = 0)
include hcomm hst hnil

theorem GlobalTheory.GenEigenFinOrbit.finrank_map_prod_le [FiniteDimensional ℂ N] (gs : List (End ℂ V))
    (hgs : ∀ g ∈ gs, g ∈ G) :
    finrank ℂ (N.map gs.prod) ≤ finrank ℂ N - gs.length := by sorry
