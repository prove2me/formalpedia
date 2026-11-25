-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_tailSum_le_sum
-- name    : GroundTheory.Automorphic.Spherical.tailSum_le_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:35:28.165617+00:00
-- url     : https://prove2.me/theorems/2a00affb-baf9-4e19-900e-84c3887f05b0
-- title:
--   Spherical: tail Sum le sum
-- statement:
--   The Spherical construction uses the tail Sum le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L94-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L94-L133

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

theorem GroundTheory.Automorphic.Spherical.tailSum_le_sum {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n) (S : Finset (Fin n))
    (hS : S.card = m) : tailSum ν hm ≤ ∑ i ∈ S, ν i := by sorry
