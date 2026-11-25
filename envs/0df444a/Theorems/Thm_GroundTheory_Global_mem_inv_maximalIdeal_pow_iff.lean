-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_inv_maximalIdeal_pow_iff
-- name    : GroundTheory.Global.mem_inv_maximalIdeal_pow_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:20.518798+00:00
-- url     : https://prove2.me/theorems/32c0f705-f695-566c-b7da-f7dad8b5a6bc
-- title:
--   Global: mem inv maximal Ideal pow iff
-- statement:
--   The Global construction uses the mem inv maximal Ideal pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L24-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminantLocal.lean#L24-L55

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
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion M)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion M)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion M)]

theorem GroundTheory.Global.mem_inv_maximalIdeal_pow_iff {F : Type*} [Field F] [NumberField F]
    (u : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : u.adicCompletion F) :
    y ∈ ((𝓂[u.adicCompletion F] ^ n : Ideal 𝒪[u.adicCompletion F]) :
      FractionalIdeal (nonZeroDivisors 𝒪[u.adicCompletion F]) (u.adicCompletion F))⁻¹ ↔
      Valued.v y ≤ WithZero.exp (n : ℤ) := by sorry
