-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvolRes_residue_pow_and_roots
-- name    : GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:30.438384+00:00
-- url     : https://prove2.me/theorems/0a81aafa-61e6-4e5d-a016-c95bd48552b5
-- title:
--   Invol Res: residue pow and roots
-- statement:
--   The Invol Res construction uses the residue pow and roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionResiduePowAndRootsOfUnity.lean#L8-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/InvolutionResiduePowAndRootsOfUnity.lean#L8-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.InvolRes

theorem GlobalTheory.UnitLemma.InvolRes.residue_pow_and_roots : ∀ (S : Type) [CommRing S] [IsLocalRing S] [Finite (ResidueField S)] (M : ℕ),
    Nat.card (ResidueField S) = M ^ 2 → ∀ τ : S →+* S, (∀ x, τ (τ x) = x) →
    (∃ x, residue S (τ x) ≠ residue S x) →
    (∀ x, residue S (τ x) = residue S x ^ M) ∧ ∀ w : S, w ^ (M ^ 2 - 1) = 1 → τ w = w ^ M := by sorry
