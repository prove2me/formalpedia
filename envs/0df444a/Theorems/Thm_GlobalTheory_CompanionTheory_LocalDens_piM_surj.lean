-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_piM_surj
-- name    : GlobalTheory.CompanionTheory.LocalDens.piM_surj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:46.312842+00:00
-- url     : https://prove2.me/theorems/1d5f4909-71f9-4b69-b28e-87b8ffba5cc1
-- title:
--   Local Dens: pi M surj
-- statement:
--   The Local Dens construction uses the pi M surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L225-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L225-L228

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

theorem GlobalTheory.CompanionTheory.LocalDens.piM_surj (ϖ : R) (k a b : ℕ) : Function.Surjective (piM ϖ k a b) := by sorry
