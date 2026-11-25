-- Prove2me | Theorems.Thm_GroundTheory_Global_cosetAverage_inertia_eq
-- name    : GroundTheory.Global.cosetAverage_inertia_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:24.413579+00:00
-- url     : https://prove2.me/theorems/7c11de26-1407-4436-b05d-d5b9f83fe78b
-- title:
--   Global: coset Average inertia eq
-- statement:
--   The Global construction uses the coset Average inertia eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L83-L95

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (v : HeightOneSpectrum (𝓞 K))

theorem GroundTheory.Global.cosetAverage_inertia_eq (f : Gal(L/K) → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g)
    (w w' : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    [w'.asIdeal.LiesOver v.asIdeal] {φ φ' : Gal(L/K)} (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal)
    (hφ' : IsArithFrobAt (𝓞 K) φ' w'.asIdeal) (m : ℕ) :
    cosetAverage (w'.asIdeal.inertia Gal(L/K)) f (φ' ^ m) =
      cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) := by sorry
