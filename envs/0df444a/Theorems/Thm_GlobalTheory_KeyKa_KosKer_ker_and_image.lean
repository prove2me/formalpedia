-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KosKer_ker_and_image
-- name    : GlobalTheory.KeyKa.KosKer.ker_and_image
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:13.149822+00:00
-- url     : https://prove2.me/theorems/7648c3a1-8efb-4417-919e-c85e9d26751f
-- title:
--   Kos Ker: ker and image
-- statement:
--   The Kos Ker construction uses the ker and image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulVecCongrDeg.lean#L125-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MulVecCongrDeg.lean#L125-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MulVecCongrDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosKer
open Matrix
variable {g d : ℕ} {N : ℕ → ℕ}

theorem GlobalTheory.KeyKa.KosKer.ker_and_image : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by sorry
