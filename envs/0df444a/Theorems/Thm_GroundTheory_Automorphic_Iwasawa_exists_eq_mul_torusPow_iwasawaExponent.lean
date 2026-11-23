-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Iwasawa_exists_eq_mul_torusPow_iwasawaExponent
-- name    : GroundTheory.Automorphic.Iwasawa.exists_eq_mul_torusPow_iwasawaExponent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:22.542693+00:00
-- url     : https://prove2.me/theorems/dd2fb4d9-be9c-42ef-9e18-0270127d7031
-- title:
--   Iwasawa: exists eq mul torus Pow iwasawa Exponent
-- statement:
--   The Iwasawa construction uses the exists eq mul torus Pow iwasawa Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L448-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Iwasawa.lean#L448-L452

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
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
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Iwasawa.exists_eq_mul_torusPow_iwasawaExponent (g : GL (Fin n) F) :
    ∃ u ∈ unipotent F n, ∃ k ∈ integralGL F n,
      g = u * torusPow F n (iwasawaExponent F n g) * k := by sorry
