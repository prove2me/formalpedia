-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_mem_tangentDerivations_mul_eq
-- name    : FunctorialResolution.EmbeddedResolution.exists_mem_tangentDerivations_mul_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:09.313717+00:00
-- url     : https://prove2.me/theorems/1c177b85-acc3-49fc-af74-1d6a181d9235
-- title:
--   Embedded Resolution: exists mem tangent Derivations mul eq
-- statement:
--   The Embedded Resolution construction uses the exists mem tangent Derivations mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L110-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/DerivativeIdeal/LogDerivativeIdealLocalization.lean#L110-L153

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']

theorem FunctorialResolution.EmbeddedResolution.exists_mem_tangentDerivations_mul_eq (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by sorry
