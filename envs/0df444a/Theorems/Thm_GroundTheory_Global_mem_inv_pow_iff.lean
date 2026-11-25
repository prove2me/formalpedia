-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_inv_pow_iff
-- name    : GroundTheory.Global.mem_inv_pow_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:50.974794+00:00
-- url     : https://prove2.me/theorems/6b6b5b96-03c5-41e8-a102-73c4ca829806
-- title:
--   Global: mem inv pow iff
-- statement:
--   The Global construction uses the mem inv pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L86-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L86-L138

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_NormTrace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminantLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.LocalField
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {M : Type*} [Field M] [NumberField M]

theorem GroundTheory.Global.mem_inv_pow_iff (w : HeightOneSpectrum (𝓞 M)) (n : ℕ) (x : M) :
    x ∈ ((w.asIdeal ^ n : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      w.valuation M x ≤ WithZero.exp (n : ℤ) ∧
        ∀ u : HeightOneSpectrum (𝓞 M), u ≠ w → u.valuation M x ≤ 1 := by sorry
