-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_fin
-- name    : GlobalTheory.CompanionTheory.Descent.acyc_fin
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:40.294064+00:00
-- url     : https://prove2.me/theorems/17cf33c4-c8e7-4201-9961-5847dcdab32e
-- title:
--   Descent: acyc fin
-- statement:
--   The Descent construction uses the acyc fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L97-L101

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]

theorem GlobalTheory.CompanionTheory.Descent.acyc_fin (hA : AffAcycSt) {Q : Type} [SemilatticeInf Q] [Finite Q] (v : Q →o X.affineOpens)
    (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1) (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1)
    (hcov : ⨆ a, (v a).1 = W.1) : Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by sorry
