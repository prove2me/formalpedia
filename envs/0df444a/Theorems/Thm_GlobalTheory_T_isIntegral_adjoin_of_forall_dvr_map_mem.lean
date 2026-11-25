-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_adjoin_of_forall_dvr_map_mem
-- name    : GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:22.696614+00:00
-- url     : https://prove2.me/theorems/5d3be718-b2b4-423f-8625-3d7027d59d04
-- title:
--   T: is Integral adjoin of forall dvr map mem
-- statement:
--   The T construction uses the is Integral adjoin of forall dvr map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralAdjoinOfForallCdvrStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralAdjoinOfForallCdvrStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvr
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvrStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Pj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_adjoin_of_forall_dvr_map_mem : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (gens : Finset Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → ∀ x : Ω, (∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr, (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) → (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) → IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by sorry
