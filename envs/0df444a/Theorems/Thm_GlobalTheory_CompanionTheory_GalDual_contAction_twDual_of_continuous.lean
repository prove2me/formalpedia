-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GalDual_contAction_twDual_of_continuous
-- name    : GlobalTheory.CompanionTheory.GalDual.contAction_twDual_of_continuous
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:42:10.532929+00:00
-- url     : https://prove2.me/theorems/3a1b7b13-7018-433a-aba0-eade493b4b90
-- title:
--   Gal Dual: cont Action tw Dual of continuous
-- statement:
--   The Gal Dual construction uses the cont Action tw Dual of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SelmerGroupDualExact.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SelmerGroupDualExact.lean#L8-L32

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GalDual

theorem GlobalTheory.CompanionTheory.GalDual.contAction_twDual_of_continuous {R Γ M : Type*} [CommRing R] [TopologicalSpace R]
    [DiscreteTopology R] [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (χ : Γ →* Rˣ)
    (hχ : Continuous χ) (ρ : Representation R Γ M) (hρ : ContAction ρ) :
    ContAction (twDual χ ρ) := by sorry
