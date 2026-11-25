-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_det_submatrix_tailEmb
-- name    : GroundTheory.Automorphic.Spherical.det_submatrix_tailEmb
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:45.709804+00:00
-- url     : https://prove2.me/theorems/476b281e-4bf7-51c9-ae71-93f404414318
-- title:
--   Spherical: det submatrix tail Emb
-- statement:
--   The Spherical construction uses the det submatrix tail Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L209-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L209-L223

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

theorem GroundTheory.Automorphic.Spherical.det_submatrix_tailEmb {u : GL (Fin n) F} (hu : u ∈ unipotent F n) (l : Fin n → ℤ) {m : ℕ}
    (hm : m ≤ n) :
    (((u * torusPow F n l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).submatrix (tailEmb hm)
      (tailEmb hm)).det = (uniformizer F : F) ^ tailSum l hm := by sorry
