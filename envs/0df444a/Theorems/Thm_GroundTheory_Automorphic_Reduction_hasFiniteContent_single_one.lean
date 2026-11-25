-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_single_one
-- name    : GroundTheory.Automorphic.Reduction.hasFiniteContent_single_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:08:08.169059+00:00
-- url     : https://prove2.me/theorems/048246c1-08c0-57f2-b4c7-b906494227b6
-- title:
--   Reduction: has Finite Content single one
-- statement:
--   The Reduction construction uses the has Finite Content single one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L186-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionCore.lean#L186-L200

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

theorem GroundTheory.Automorphic.Reduction.hasFiniteContent_single_one {n : ℕ} (i : Fin n) :
    HasFiniteContent (Pi.single i (1 : 𝔸[K]) : Fin n → 𝔸[K]) := by sorry
