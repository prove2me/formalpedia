-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_tailSum_le_iwasawaExponent
-- name    : GroundTheory.Automorphic.Spherical.tailSum_le_iwasawaExponent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:29:24.178863+00:00
-- url     : https://prove2.me/theorems/0a036818-0e02-4576-8b49-dc5cbf89531d
-- title:
--   Spherical: tail Sum le iwasawa Exponent
-- statement:
--   The Spherical construction uses the tail Sum le iwasawa Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L234-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalTriangular.lean#L234-L249

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

theorem GroundTheory.Automorphic.Spherical.tailSum_le_iwasawaExponent {ν : Fin n → ℤ} (hν : Cartan.IsDominant ν) {g : GL (Fin n) F}
    (hg : g ∈ DoubleCoset.doubleCoset (Cartan.diagPow F n ν)
      (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) {m : ℕ} (hm : m ≤ n) :
    tailSum ν hm ≤ tailSum (iwasawaExponent F n g) hm := by sorry
