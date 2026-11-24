-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GaloisCoh_finite_of_finite_ker
-- name    : GlobalTheory.CompanionTheory.GaloisCoh.finite_of_finite_ker
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:22.066255+00:00
-- url     : https://prove2.me/theorems/ea6d555e-2f34-4637-9d00-77a75e9848de
-- title:
--   Galois Coh: finite of finite ker
-- statement:
--   The Galois Coh construction uses the finite of finite ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesFormula.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesFormula.lean#L13-L28

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GreenbergWilesFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaloisCoh

theorem GlobalTheory.CompanionTheory.GaloisCoh.finite_of_finite_ker {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Finite B] (f : A →ₗ[R] B)
    (hk : Finite (LinearMap.ker f)) : Finite A := by sorry
