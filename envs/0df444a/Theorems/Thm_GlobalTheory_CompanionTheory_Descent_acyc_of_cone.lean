-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_cone
-- name    : GlobalTheory.CompanionTheory.Descent.acyc_of_cone
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:26:00.628745+00:00
-- url     : https://prove2.me/theorems/8b42a13d-5111-4691-a138-50c4e9764e22
-- title:
--   Descent: acyc of cone
-- statement:
--   The Descent construction uses the acyc of cone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L142-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsFiniteCover.lean#L142-L172

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

theorem GlobalTheory.CompanionTheory.Descent.acyc_of_cone (hCx : CxSt) (hHt : HtpySt) (hA : AffAcycSt) [Quiver.IsThin E] (f : E ⥤ AffOp X)
    (W : X.affineOpens) (hle) (t : E) (ht : W.1 ≤ (f.obj t).unop.1) (e : E ⥤ E)
    (a₁ : ∀ T, T ⟶ e.obj T) (a₂ : ∀ T, t ⟶ e.obj T)
    (he : ∀ T, (f.obj T).unop.1 ≤ (f.obj (e.obj T)).unop.1) : Acyc s f W.1 hle := by sorry
