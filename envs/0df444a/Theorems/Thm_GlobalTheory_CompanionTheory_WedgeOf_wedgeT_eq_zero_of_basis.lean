-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_eq_zero_of_basis
-- name    : GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_basis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:34:03.167831+00:00
-- url     : https://prove2.me/theorems/e11cc586-8037-4416-abb8-c049f729f339
-- title:
--   Wedge Of: wedge T eq zero of basis
-- statement:
--   The Wedge Of construction uses the wedge T eq zero of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L38-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L38-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_basis {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R V)
    (t : V ⊗[R] V) (ht : TensorProduct.comm R V V t = t) : wedgeT (R := R) V t = 0 := by sorry
