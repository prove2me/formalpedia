-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_card_fibers
-- name    : GlobalTheory.CompanionTheory.LocalDens.card_fibers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:37.432481+00:00
-- url     : https://prove2.me/theorems/e6a9294a-4847-4974-87a8-f0cf1323b7bc
-- title:
--   Local Dens: card fibers
-- statement:
--   The Local Dens construction uses the card fibers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean#L183-L188

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

theorem GlobalTheory.CompanionTheory.LocalDens.card_fibers {α β : Type} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (hf : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by sorry
