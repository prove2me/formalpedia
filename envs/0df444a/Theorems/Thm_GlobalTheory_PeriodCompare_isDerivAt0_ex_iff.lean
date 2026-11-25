-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCompare_isDerivAt0_ex_iff
-- name    : GlobalTheory.PeriodCompare.isDerivAt0_ex_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:22.811182+00:00
-- url     : https://prove2.me/theorems/054048e0-d2fe-558d-a737-fb53755b3170
-- title:
--   Period Compare: is Deriv At0 ex iff
-- statement:
--   The Period Compare construction uses the is Deriv At0 ex iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L335-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsDerivAt0NotIsDerivAlong.lean#L335-L342

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDerivAt0NotIsDerivAlong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTypeFn IsThetaFrame
open GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation hiding IsTypeFn IsThetaFrame
open scoped TensorProduct Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)

theorem GlobalTheory.PeriodCompare.isDerivAt0_ex_iff {P : (Fu.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (Fu.Di i) ty P) (w : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w v ↔ IsDerivAlong (fun z => (Fu.ex i P z).left) w v := by sorry
