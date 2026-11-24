-- Prove2me | Theorems.Thm_GlobalTheory_exists_root_lift_of_residue_map
-- name    : GlobalTheory.exists_root_lift_of_residue_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:54.235926+00:00
-- url     : https://prove2.me/theorems/95d31343-d348-4f05-bfd8-c916694bda90
-- title:
--   Global Theory: exists root lift of residue map
-- statement:
--   The Global Theory construction uses the exists root lift of residue map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidue.lean#L11-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidue.lean#L11-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory

theorem GlobalTheory.exists_root_lift_of_residue_map :
    ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V]
      [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V)
      (σ : ResidueField R →+* ResidueField V),
      (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic →
      (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) →
      ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by sorry
