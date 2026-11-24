-- Prove2me | Theorems.Thm_GlobalTheory_Phase_GaussSum_twist
-- name    : GlobalTheory.Phase.GaussSum.twist
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:35.555853+00:00
-- url     : https://prove2.me/theorems/27053e5c-d359-4b48-9cc5-ed5a58162732
-- title:
--   Gauss Sum: twist
-- statement:
--   The Gauss Sum construction uses the twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L8-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean#L8-L49

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

theorem GlobalTheory.Phase.GaussSum.twist {N W : Type} [AddCommGroup N] [Fintype N] [AddCommGroup W] (e : W → ℂ)
    (he : ∀ s t, e (s + t) = e s * e t) (hc : ∀ t, e (-t) = conj (e t)) (h0 : e 0 = 1)
    (Q : N → W) (B : N →+ N →+ W) (hQ : ∀ x y, Q (x + y) = Q x + Q y + B x y) (ψ : N →+ W)
    (hT : ∑ x, e (Q x) = ∑ x, e (ψ x - Q x)) :
    ∑ x, e (Q x) = 0 ∨ ∃ a, ∑ x, e (Q x) = e (Q a) * conj (∑ x, e (Q x)) := by sorry
