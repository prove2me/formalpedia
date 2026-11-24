-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PosDirichlet_hasSum_mul_of_norm_summable
-- name    : GlobalTheory.Mem.PosDirichlet.hasSum_mul_of_norm_summable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:23:22.833909+00:00
-- url     : https://prove2.me/theorems/e69ce93c-095f-4d6c-af0b-46cf275254f6
-- title:
--   Pos Dirichlet: has Sum mul of norm summable
-- statement:
--   The Pos Dirichlet construction uses the has Sum mul of norm summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/DedekindZetaFactorizationRay.lean#L25-L27

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

theorem GlobalTheory.Mem.PosDirichlet.hasSum_mul_of_norm_summable {ι κ : Type} {f : ι → ℂ} {g : κ → ℂ} {a b : ℂ} (hf : HasSum f a)
    (hg : HasSum g b) : HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) := by sorry
