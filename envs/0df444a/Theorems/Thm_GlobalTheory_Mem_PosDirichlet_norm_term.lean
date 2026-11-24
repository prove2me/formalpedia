-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PosDirichlet_norm_term
-- name    : GlobalTheory.Mem.PosDirichlet.norm_term
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:24:39.829785+00:00
-- url     : https://prove2.me/theorems/eb3f916f-09a2-429b-93c0-686e9160867c
-- title:
--   Pos Dirichlet: norm term
-- statement:
--   The Pos Dirichlet construction uses the norm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L51-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
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
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet

theorem GlobalTheory.Mem.PosDirichlet.norm_term {w : ℝ} (hw : 0 ≤ w) {N : ℕ} (hN : N ≠ 0) (s : ℂ) :
    ‖(w : ℂ) * (N : ℂ) ^ (-s)‖ = ((w : ℂ) * (N : ℂ) ^ (-(s.re : ℂ))).re := by sorry
