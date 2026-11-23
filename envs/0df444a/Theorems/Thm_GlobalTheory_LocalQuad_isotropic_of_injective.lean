-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_isotropic_of_injective
-- name    : GlobalTheory.LocalQuad.isotropic_of_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:53.760079+00:00
-- url     : https://prove2.me/theorems/9b649e26-58f9-4af8-ab65-21a63571beaf
-- title:
--   Local Quad: isotropic of injective
-- statement:
--   The Local Quad construction uses the isotropic of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L139-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsQuaternaryOfCoordinates.lean#L139-L154

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
variable {k : Type*} [Field k]

theorem GlobalTheory.LocalQuad.isotropic_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι)
    (he : Function.Injective e) {a : ι → k}
    (h : ∃ x : κ → k, x ≠ 0 ∧ ∑ j, a (e j) * x j ^ 2 = 0) :
    ∃ x : ι → k, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by sorry
