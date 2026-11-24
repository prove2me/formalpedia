-- Prove2me | Theorems.Thm_GlobalTheory_LatBasisAt_mem_locRing
-- name    : GlobalTheory.LatBasisAt.mem_locRing
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:06.118816+00:00
-- url     : https://prove2.me/theorems/12fc5fba-6d73-44be-8ad1-5fa354669709
-- title:
--   Lat Basis At: mem loc Ring
-- statement:
--   The Lat Basis At construction uses the mem loc Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L16-L19

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

theorem GlobalTheory.LatBasisAt.mem_locRing (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locRing w ↔ ∃ (a s : 𝓞 K) (_ : s ∉ w.asIdeal),
      x = algebraMap (𝓞 K) K a * (algebraMap (𝓞 K) K s)⁻¹ := by sorry
