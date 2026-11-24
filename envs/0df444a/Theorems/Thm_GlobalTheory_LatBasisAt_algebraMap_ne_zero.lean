-- Prove2me | Theorems.Thm_GlobalTheory_LatBasisAt_algebraMap_ne_zero
-- name    : GlobalTheory.LatBasisAt.algebraMap_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:01.426571+00:00
-- url     : https://prove2.me/theorems/a069735d-2dfc-4aee-b5fb-a54b347173ae
-- title:
--   Lat Basis At: algebra Map ne zero
-- statement:
--   The Lat Basis At construction uses the algebra Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L21-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open GlobalTheory GlobalTheory.LatBasisAt
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.LatBasisAt.algebraMap_ne_zero (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K}
    (hs : s ∉ w.asIdeal) : algebraMap (𝓞 K) K s ≠ 0 := by sorry
