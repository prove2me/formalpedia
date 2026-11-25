-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_tailSum_succ
-- name    : GroundTheory.Automorphic.Spherical.tailSum_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:34.188803+00:00
-- url     : https://prove2.me/theorems/a4230900-199e-5eed-80e7-492d4b718c43
-- title:
--   Spherical: tail Sum succ
-- statement:
--   The Spherical construction uses the tail Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L272-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L272-L279

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

theorem GroundTheory.Automorphic.Spherical.tailSum_succ (l : Fin n → ℤ) {m : ℕ} (hm : m + 1 ≤ n) :
    tailSum l hm = l ⟨n - (m + 1), by omega⟩ + tailSum l (Nat.le_of_succ_le hm) := by sorry
