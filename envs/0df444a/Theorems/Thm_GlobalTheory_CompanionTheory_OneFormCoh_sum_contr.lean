-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OneFormCoh_sum_contr
-- name    : GlobalTheory.CompanionTheory.OneFormCoh.sum_contr
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:04.424032+00:00
-- url     : https://prove2.me/theorems/fc39be92-582f-4818-b77c-a5e2d954f5e9
-- title:
--   One Form Coh: sum contr
-- statement:
--   The One Form Coh construction uses the sum contr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtendedFormNaturality.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExtendedFormNaturality.lean#L95-L104

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExtendedFormNaturality
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OneFormCoh
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.OneFormCoh.sum_contr {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Glob1 F →ₗ[R] R)
    (hw : ∀ v, ∑ i, l i v • w i = v) (t : Z1 F ⊗[R] Glob1 F) :
    ∑ i, contr F (l i) t ⊗ₜ[R] w i = t := by sorry
