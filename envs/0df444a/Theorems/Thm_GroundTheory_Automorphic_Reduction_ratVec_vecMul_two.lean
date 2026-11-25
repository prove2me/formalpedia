-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_vecMul_two
-- name    : GroundTheory.Automorphic.Reduction.ratVec_vecMul_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:08:01.835511+00:00
-- url     : https://prove2.me/theorems/b0052578-01fd-594d-b6f1-0c7528988a72
-- title:
--   Reduction: rat Vec vec Mul two
-- statement:
--   The Reduction construction uses the rat Vec vec Mul two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L211-L215

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionFinite
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionBlock
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionDirichlet
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Reduction.ratVec_vecMul_two (x : Fin 2 → K) (α u β : 𝔸[K]) :
    ratVec x ᵥ* !![α, u; 0, β] =
      ![algebraMap K 𝔸[K] (x 0) * α, algebraMap K 𝔸[K] (x 0) * u + algebraMap K 𝔸[K] (x 1) * β] := by sorry
