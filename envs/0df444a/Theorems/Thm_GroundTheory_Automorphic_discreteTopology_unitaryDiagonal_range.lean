-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_discreteTopology_unitaryDiagonal_range
-- name    : GroundTheory.Automorphic.discreteTopology_unitaryDiagonal_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:03:22.608777+00:00
-- url     : https://prove2.me/theorems/5dbf3e79-6f7c-501b-a8ca-ed4b6b00abe5
-- title:
--   Automorphic: discrete Topology unitary Diagonal range
-- statement:
--   The Automorphic construction uses the discrete Topology unitary Diagonal range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups.lean#L109-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups.lean#L109-L127

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_LatticeCompact
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable [NumberField K]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

theorem GroundTheory.Automorphic.discreteTopology_unitaryDiagonal_range :
    DiscreteTopology (unitaryDiagonal K H).range := by sorry
