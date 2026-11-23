-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_solCount_eq
-- name    : GlobalTheory.CompanionTheory.LocalDens.solCount_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:18.654228+00:00
-- url     : https://prove2.me/theorems/c806b05d-7449-4789-a10f-0735da7868f5
-- title:
--   Local Dens: sol Count eq
-- statement:
--   The Local Dens construction uses the sol Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L109-L110

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

theorem GlobalTheory.CompanionTheory.LocalDens.solCount_eq (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) : solCount σ ϖ S T k = Nat.card (sol σ ϖ S T k) := by sorry
