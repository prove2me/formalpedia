-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_single_add_single
-- name    : GroundTheory.Automorphic.Reduction.euclidNorm_single_add_single
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:08:14.622237+00:00
-- url     : https://prove2.me/theorems/fbaa112b-d541-5b2c-a02e-078cd1ffd487
-- title:
--   Reduction: euclid Norm single add single
-- statement:
--   The Reduction construction uses the euclid Norm single add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L40-L46

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
variable {E : Type*} [NormedField E] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.euclidNorm_single_add_single {i i' : Fin n} (h : i ≠ i') (x y : E) :
    euclidNorm (Pi.single i x + Pi.single i' y : Fin n → E) = euclidNorm ![x, y] := by sorry
