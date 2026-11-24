-- Prove2me | Theorems.Thm_GlobalTheory_LatBasisAt_mem_localization_iff
-- name    : GlobalTheory.LatBasisAt.mem_localization_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:43.621205+00:00
-- url     : https://prove2.me/theorems/8d66ca6d-b291-4524-b775-18a631574fac
-- title:
--   Lat Basis At: mem localization iff
-- statement:
--   The Lat Basis At construction uses the mem localization iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L27-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LatticeHasBasisAtEveryFinitePlace
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

theorem GlobalTheory.LatBasisAt.mem_localization_iff (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ M := by sorry
