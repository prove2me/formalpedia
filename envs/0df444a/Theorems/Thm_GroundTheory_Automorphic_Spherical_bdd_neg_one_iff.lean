-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_bdd_neg_one_iff
-- name    : GroundTheory.Automorphic.Spherical.bdd_neg_one_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:22.618219+00:00
-- url     : https://prove2.me/theorems/cc3bc4a6-3b76-5887-8311-3ade0e6ebb95
-- title:
--   Spherical: bdd neg one iff
-- statement:
--   The Spherical construction uses the bdd neg one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L52-L60

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalTriangular
import Definitions.Def_GroundTheory_AutomorphicForms_SphericalMinuscule
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
open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra
open ValuativeRel (valuation)
open scoped ValuativeRel
open GroundTheory.Automorphic.Spherical
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
local notation "π" => (GLnLocal.uniformizer F : F)

theorem GroundTheory.Automorphic.Spherical.bdd_neg_one_iff {x : F} : Bdd F (-1) x ↔ π * x ∈ 𝒪[F] := by sorry
