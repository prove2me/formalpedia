-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_hensel_root_residue
-- name    : GlobalTheory.T.exists_hensel_root_residue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:23.398017+00:00
-- url     : https://prove2.me/theorems/0def6ff1-ded5-4dde-ad42-0550c93ce372
-- title:
--   T: exists hensel root residue
-- statement:
--   The T construction uses the exists hensel root residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidueStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHenselRootResidueStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidue
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHenselRootResidueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_hensel_root_residue : ∀ {A R V : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsAdicComplete (maximalIdeal V) V] (φ : A →+* R) (α : A →+* V) (σ : ResidueField R →+* ResidueField V), (∀ a, σ (residue R (φ a)) = residue V (α a)) → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → IsUnit ((q.derivative.map φ).eval θ) → ∃ η : V, (q.map α).eval η = 0 ∧ residue V η = σ (residue R θ) := by sorry
