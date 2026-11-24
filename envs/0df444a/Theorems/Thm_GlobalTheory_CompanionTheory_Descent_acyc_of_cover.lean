-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_cover
-- name    : GlobalTheory.CompanionTheory.Descent.acyc_of_cover
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:25:50.439168+00:00
-- url     : https://prove2.me/theorems/6fdcc357-1462-4f23-bcf3-1d9103efc1da
-- title:
--   Descent: acyc of cover
-- statement:
--   The Descent construction uses the acyc of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L276-L321
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L276-L321

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
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
include hi

theorem GlobalTheory.CompanionTheory.Descent.acyc_of_cover (hCx : CxSt) (hHt : HtpySt) (hQ : QCalcSt) (hFub : FubiniSt) (hA : AffAcycSt)
    {P : Type} [SemilatticeInf P] (v : P →o X.affineOpens)
    (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1) (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1)
    (hcov : ⨆ a, (v a).1 = W.1) :
    Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by sorry
