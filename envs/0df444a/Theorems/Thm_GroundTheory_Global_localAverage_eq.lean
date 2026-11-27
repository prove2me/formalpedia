-- Prove2me | Theorems.Thm_GroundTheory_Global_localAverage_eq
-- name    : GroundTheory.Global.localAverage_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:12.915347+00:00
-- url     : https://prove2.me/theorems/c580c922-6b5d-51cd-9e77-3b88cb107fe3
-- title:
--   Global: local Average eq
-- statement:
--   The Global construction uses the local Average eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MemInvariantsCompSubtypeIff.lean#L116-L120

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

theorem GroundTheory.Global.localAverage_eq (f : Gal(L/K) → ℂ) (hf : ∀ g h, f (h * g * h⁻¹) = f g)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] {φ : Gal(L/K)}
    (hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal) (m : ℕ) :
    localAverage L v f m = cosetAverage (w.asIdeal.inertia Gal(L/K)) f (φ ^ m) := by sorry
