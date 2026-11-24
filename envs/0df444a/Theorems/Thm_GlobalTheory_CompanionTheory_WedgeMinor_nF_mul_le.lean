-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeMinor_nF_mul_le
-- name    : GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:21:44.712557+00:00
-- url     : https://prove2.me/theorems/2b35b904-18c7-436a-b81f-68971eefe1e3
-- title:
--   Wedge Minor: n F mul le
-- statement:
--   The Wedge Minor construction uses the n F mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityFinitePlaces.lean#L48-L52

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeMinor

theorem GlobalTheory.CompanionTheory.WedgeMinor.nF_mul_le {K ι ι' κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι]
    [Fintype ι'] [Fintype κ] [DecidableEq κ] (g : Matrix ι' ι K) (A : Matrix ι κ K) :
    nF (g * A) ≤ sz g ^ Fintype.card κ * nF A := by sorry
