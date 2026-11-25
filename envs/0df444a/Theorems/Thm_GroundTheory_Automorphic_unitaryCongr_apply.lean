-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_unitaryCongr_apply
-- name    : GroundTheory.Automorphic.unitaryCongr_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:49.571884+00:00
-- url     : https://prove2.me/theorems/c32ad7c0-0da8-56f1-876a-5eead51844a7
-- title:
--   Automorphic: unitary Congr apply
-- statement:
--   The Automorphic construction uses the unitary Congr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups.lean#L43-L45

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
variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

theorem GroundTheory.Automorphic.unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap K E H (e : R →ₐ[K] S) g := by sorry
