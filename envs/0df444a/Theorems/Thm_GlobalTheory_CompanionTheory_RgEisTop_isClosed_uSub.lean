-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisTop_isClosed_uSub
-- name    : GlobalTheory.CompanionTheory.RgEisTop.isClosed_uSub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:53.507611+00:00
-- url     : https://prove2.me/theorems/dc41b75d-5a1d-46ae-bf76-0750e321ff8c
-- title:
--   Rg Eis Top: is Closed u Sub
-- statement:
--   The Rg Eis Top construction uses the is Closed u Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L60-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GeneralLinearTopologicalGroup.lean#L60-L68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GeneralLinearTopologicalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisTop
open PositivityTheory.RgEis

theorem GlobalTheory.CompanionTheory.RgEisTop.isClosed_uSub {E R : Type} [Field E] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [T2Space R] (A : Ad E R) (hσ : Continuous A.σ) (ε : ℤˣ)
    (ι : Type) [Fintype ι] [DecidableEq ι] :
    IsClosed (A.uSub ε ι : Set (GL (ι ⊕ ι) R)) := by sorry
