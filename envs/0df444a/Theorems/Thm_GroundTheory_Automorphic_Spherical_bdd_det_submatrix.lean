-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_bdd_det_submatrix
-- name    : GroundTheory.Automorphic.Spherical.bdd_det_submatrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:40.110108+00:00
-- url     : https://prove2.me/theorems/3d8c8193-5199-5031-a39e-0330778a8e57
-- title:
--   Spherical: bdd det submatrix
-- statement:
--   The Spherical construction uses the bdd det submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L135-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L135-L178

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

theorem GroundTheory.Automorphic.Spherical.bdd_det_submatrix {A B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hB : ∀ i j, B i j ∈ 𝒪[F]) {ν : Fin n → ℤ} (hν : Antitone ν) {m : ℕ} (hm : m ≤ n)
    (r c : Fin m → Fin n) :
    Bdd F (tailSum ν hm)
      ((A * diagonal (fun i => (uniformizer F : F) ^ ν i) * B).submatrix r c).det := by sorry
