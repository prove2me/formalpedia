-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_bdd_zpow
-- name    : GroundTheory.Automorphic.Spherical.bdd_zpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:15.157183+00:00
-- url     : https://prove2.me/theorems/0d6f148b-7804-4b7b-8adf-f3b93b4a5520
-- title:
--   Spherical: bdd zpow
-- statement:
--   The Spherical construction uses the bdd zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L62-L63

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalSatake
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra ValuativeRel
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Spherical.bdd_zpow (t : ℤ) : Bdd F t ((uniformizer F : F) ^ t) := by sorry
