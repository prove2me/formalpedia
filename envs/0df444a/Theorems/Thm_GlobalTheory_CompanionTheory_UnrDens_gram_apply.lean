-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_gram_apply
-- name    : GlobalTheory.CompanionTheory.UnrDens.gram_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:03.000883+00:00
-- url     : https://prove2.me/theorems/d2a014a1-7571-405e-a7f7-67266106e69b
-- title:
--   Unr Dens: gram apply
-- statement:
--   The Unr Dens construction uses the gram apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L198-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ResAlgSplitTwo.lean#L198-L206

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens
variable {E : Type} [CommRing E] {τ : E →+* E}
variable {V : Type} [AddCommGroup V] [Module E V]

theorem GlobalTheory.CompanionTheory.UnrDens.gram_apply (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E)
    (hS : cT τ S = S) (hd : IsUnit S.det) (x : Matrix (Fin m) (Fin n) E) (i j : Fin n) :
    (cT τ x * S * x) i j = (HermSp.ofMatrix hτ S hS hd).h (fun a => x a j) (fun a => x a i) := by sorry
