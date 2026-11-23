-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PosDirichlet_const
-- name    : GlobalTheory.Mem.PosDirichlet.const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:23.136621+00:00
-- url     : https://prove2.me/theorems/9968598a-490e-42af-b531-705604af319b
-- title:
--   Pos Dirichlet: const
-- statement:
--   The Pos Dirichlet construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L21-L23

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

theorem GlobalTheory.Mem.PosDirichlet.const {c : ℝ} (hc : 0 ≤ c) : PosDirichlet (fun _ => (c : ℂ)) := by sorry
