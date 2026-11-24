-- Prove2me | Theorems.Thm_GlobalTheory_Phase_GaussSum_pow_four
-- name    : GlobalTheory.Phase.GaussSum.pow_four
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:57.476393+00:00
-- url     : https://prove2.me/theorems/67a27244-fada-4aa7-93f1-a19a76dc7a0f
-- title:
--   Gauss Sum: pow four
-- statement:
--   The Gauss Sum construction uses the pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L74-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L74-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.GaussSum

theorem GlobalTheory.Phase.GaussSum.pow_four {M W : Type} [AddCommGroup M] [Fintype M] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (q : M → W) (β : M →+ M →+ W) (hq : ∀ x y, q (x + y) = q x + q y + β x y) :
    (∑ x, e (q x)) ^ 4 = 0 ∨ ∃ a : Fin 4 → M,
      (∑ x, e (q x)) ^ 4 = (∏ i, e (q (a i))) * conj ((∑ x, e (q x)) ^ 4) := by sorry
