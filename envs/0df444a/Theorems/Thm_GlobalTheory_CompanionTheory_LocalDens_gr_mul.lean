-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gr_mul
-- name    : GlobalTheory.CompanionTheory.LocalDens.gr_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:44.347415+00:00
-- url     : https://prove2.me/theorems/cbbbe7e7-46f4-4a2d-9f61-4300b9596fed
-- title:
--   Local Dens: gr mul
-- statement:
--   The Local Dens construction uses the gr mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L101-L103

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

theorem GlobalTheory.CompanionTheory.LocalDens.gr_mul (σ : R →+* R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R)
    (g : Matrix (Fin n) (Fin n) R) : gr σ S (x * g) = cT σ g * gr σ S x * g := by sorry
