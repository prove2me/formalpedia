-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_piH_surj
-- name    : GlobalTheory.CompanionTheory.LocalDens.piH_surj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:52:06.960315+00:00
-- url     : https://prove2.me/theorems/34c400a7-f970-424f-ad50-1d5fe07060f3
-- title:
--   Local Dens: pi H surj
-- statement:
--   The Local Dens construction uses the pi H surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L254-L256

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

theorem GlobalTheory.CompanionTheory.LocalDens.piH_surj (σ : R →+* R) (ϖ : R) (n k : ℕ) : Function.Surjective (piH σ ϖ n k) := by sorry
