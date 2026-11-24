-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gr_herm
-- name    : GlobalTheory.CompanionTheory.LocalDens.gr_herm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:10.319608+00:00
-- url     : https://prove2.me/theorems/21c692a1-e10e-466c-a242-63eb07c5da62
-- title:
--   Local Dens: gr herm
-- statement:
--   The Local Dens construction uses the gr herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L276-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L276-L279

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]

theorem GlobalTheory.CompanionTheory.LocalDens.gr_herm {σ : R →+* R} (hinv : ∀ a, σ (σ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) R}
    (hS : cT σ S = S) (x : Matrix (Fin m) (Fin n) R) : cT σ (gr σ S x) = gr σ S x := by sorry
