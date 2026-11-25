-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_adjoin_of_forall_cdvr
-- name    : GlobalTheory.isIntegral_adjoin_of_forall_cdvr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:58.128637+00:00
-- url     : https://prove2.me/theorems/4d0de679-937e-4222-b3e5-1c3763e407c8
-- title:
--   Global Theory: is Integral adjoin of forall cdvr
-- statement:
--   The Global Theory construction uses the is Integral adjoin of forall cdvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralAdjoinOfForallCdvr.lean#L10-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralAdjoinOfForallCdvr.lean#L10-L115

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralAdjoinOfForallCdvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Pj
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.isIntegral_adjoin_of_forall_cdvr (K Ω : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] (gens : Finset Ω)
    (hcl : Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤) (x : Ω)
    (hx : ∀ (T : CDVR), Countable (IsLocalRing.ResidueField T.V) → ∀ φ : Ω →+* T.Fr,
      (∀ k : K, φ (algebraMap K Ω k) ∈ (algebraMap T.V T.Fr).range) →
      (∀ g ∈ gens, φ g ∈ (algebraMap T.V T.Fr).range) → φ x ∈ (algebraMap T.V T.Fr).range) :
    IsIntegral (Algebra.adjoin K (gens : Set Ω)) x := by sorry
