-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PosDirichlet_pow
-- name    : GlobalTheory.Mem.PosDirichlet.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:11.848083+00:00
-- url     : https://prove2.me/theorems/6a62f689-6695-47ce-ae68-4c5c2f9e347c
-- title:
--   Pos Dirichlet: pow
-- statement:
--   The Pos Dirichlet construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L46-L49

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

theorem GlobalTheory.Mem.PosDirichlet.pow {F : ℂ → ℂ} (hF : PosDirichlet F) (j : ℕ) : PosDirichlet (fun s => F s ^ j) := by sorry
