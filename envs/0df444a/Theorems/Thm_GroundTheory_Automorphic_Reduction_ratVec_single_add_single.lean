-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_single_add_single
-- name    : GroundTheory.Automorphic.Reduction.ratVec_single_add_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:49.257561+00:00
-- url     : https://prove2.me/theorems/f6626f6d-2d33-596c-9c29-43dad1b66aef
-- title:
--   Reduction: rat Vec single add single
-- statement:
--   The Reduction construction uses the rat Vec single add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L217-L223

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

theorem GroundTheory.Automorphic.Reduction.ratVec_single_add_single {n : ℕ} (i i' : Fin n) (a c : K) :
    ratVec (Pi.single i a + Pi.single i' c : Fin n → K) =
      Pi.single i (algebraMap K 𝔸[K] a) + Pi.single i' (algebraMap K 𝔸[K] c) := by sorry
