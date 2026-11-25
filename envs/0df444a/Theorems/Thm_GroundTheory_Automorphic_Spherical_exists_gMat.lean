-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Spherical_exists_gMat
-- name    : GroundTheory.Automorphic.Spherical.exists_gMat
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:35.817989+00:00
-- url     : https://prove2.me/theorems/5f243f39-0469-4343-aa7a-64ad943a35a1
-- title:
--   Spherical: exists g Mat
-- statement:
--   The Spherical construction uses the exists g Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L282-L483
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalMinuscule.lean#L282-L483

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

theorem GroundTheory.Automorphic.Spherical.exists_gMat {k : ℕ} {g : GL (Fin n) F} (hg : g ∈ minusculeSet F n k) :
    ∃ S : Finset (Fin n), S.card = k ∧ ∃ c : Pairs S → 𝓀[F],
      (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk g := by sorry
