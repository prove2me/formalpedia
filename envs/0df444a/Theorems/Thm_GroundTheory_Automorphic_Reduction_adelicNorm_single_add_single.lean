-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_single_add_single
-- name    : GroundTheory.Automorphic.Reduction.adelicNorm_single_add_single
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:11:26.80481+00:00
-- url     : https://prove2.me/theorems/0bc3daa2-5bff-402f-9c7f-7123a0f3e428
-- title:
--   Reduction: adelic Norm single add single
-- statement:
--   The Reduction construction uses the adelic Norm single add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L71-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L71-L97

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

theorem GroundTheory.Automorphic.Reduction.adelicNorm_single_add_single {n : ℕ} {i i' : Fin n} (h : i ≠ i') (a c : 𝔸[K]) :
    adelicNorm (Pi.single i a + Pi.single i' c : Fin n → 𝔸[K]) = adelicNorm ![a, c] := by sorry
