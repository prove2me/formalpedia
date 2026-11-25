-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_dens_step
-- name    : GlobalTheory.CompanionTheory.LocalDens.dens_step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:42.404787+00:00
-- url     : https://prove2.me/theorems/296812d5-2560-4bc5-a42a-3a6cf3b19913
-- title:
--   Local Dens: dens step
-- statement:
--   The Local Dens construction uses the dens step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L281-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L281-L340

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

theorem GlobalTheory.CompanionTheory.LocalDens.dens_step {σ : R →+* R} {ϖ : R} (hfin : ∀ k, Finite (R ⧸ lev ϖ k)) (hinv : ∀ a, σ (σ a) = a)
    (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ)
    (hS : cT σ S = S) (hT : cT σ T = T)
    (hfib : ∀ h : Matrix (Fin n) (Fin n) R, cT σ h = h → red ϖ k h = red ϖ k T →
      solCount σ ϖ S h (k + 1) = solCount σ ϖ S T (k + 1)) :
    densAt σ ϖ S T k = densAt σ ϖ S T (k + 1) := by sorry
