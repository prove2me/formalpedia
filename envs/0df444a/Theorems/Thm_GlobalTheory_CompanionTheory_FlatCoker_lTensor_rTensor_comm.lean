-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FlatCoker_lTensor_rTensor_comm
-- name    : GlobalTheory.CompanionTheory.FlatCoker.lTensor_rTensor_comm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:56.923178+00:00
-- url     : https://prove2.me/theorems/d61d483e-a2a7-44b8-8ed1-1c7f603648b0
-- title:
--   Flat Coker: l Tensor r Tensor comm
-- statement:
--   The Flat Coker construction uses the l Tensor r Tensor comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FlatQuotientOfUniversallyInjective.lean#L6-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FlatQuotientOfUniversallyInjective.lean#L6-L13

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FlatQuotientOfUniversallyInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlatCoker

theorem GlobalTheory.CompanionTheory.FlatCoker.lTensor_rTensor_comm {R P Q X Y : Type} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (i : P →ₗ[R] Q) (g : X →ₗ[R] Y) (t : P ⊗[R] X) :
    g.lTensor Q (i.rTensor X t) = i.rTensor Y (g.lTensor P t) := by sorry
