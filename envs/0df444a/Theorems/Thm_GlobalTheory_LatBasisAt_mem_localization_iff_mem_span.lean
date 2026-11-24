-- Prove2me | Theorems.Thm_GlobalTheory_LatBasisAt_mem_localization_iff_mem_span
-- name    : GlobalTheory.LatBasisAt.mem_localization_iff_mem_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:53.646035+00:00
-- url     : https://prove2.me/theorems/d35a54de-4e3d-4f92-b803-fe80a2e31f2e
-- title:
--   Lat Basis At: mem localization iff mem span
-- statement:
--   The Lat Basis At construction uses the mem localization iff mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L32-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LatticeHasBasisAtEveryFinitePlace.lean#L32-L64

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

theorem GlobalTheory.LatBasisAt.mem_localization_iff_mem_span (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (M : Submodule (𝓞 K) (Fin d → K))
    (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ↔ x ∈ Submodule.span (locRing w) (M : Set (Fin d → K)) := by sorry
