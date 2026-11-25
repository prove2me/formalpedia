-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PrincipalLatDVR_eq_mulLat_integralClosure_of_separable
-- name    : GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:07.128805+00:00
-- url     : https://prove2.me/theorems/acbba960-e2ba-4876-9d01-e797698d0fae
-- title:
--   Principal Lat DVR: eq mul Lat integral Closure of separable
-- statement:
--   The Principal Lat DVR construction uses the eq mul Lat integral Closure of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparabl.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqSubmoduleMulLeftImageIntegralClosureOfSeparabl.lean#L89-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PrincipalLatDVR

theorem GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A]
    [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N →
    (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) →
    ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by sorry
