-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_wedgeF_of_mulF
-- name    : GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:54.180867+00:00
-- url     : https://prove2.me/theorems/1bf07c52-d65b-4024-9be8-7f84f6d46501
-- title:
--   Wedge: wedge F of mul F
-- statement:
--   The Wedge construction uses the wedge F of mul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L268-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L268-L274

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem GlobalTheory.CompanionTheory.Wedge.wedgeF_of_mulF : MulF → WedgeF := by sorry
