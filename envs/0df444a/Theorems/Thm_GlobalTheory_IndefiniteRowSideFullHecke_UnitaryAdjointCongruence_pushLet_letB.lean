-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryAdjointCongruence_pushLet_letB
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet_letB
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:55.044232+00:00
-- url     : https://prove2.me/theorems/627259ee-2ad1-44dd-906c-9a335e9e4fae
-- title:
--   Unitary Adjoint Congruence: push Let let B
-- statement:
--   The Unitary Adjoint Congruence construction uses the push Let let B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaSpanAdjoint.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ThetaSpanAdjoint.lean#L64-L72

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaSpanAdjoint
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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open NumberField MvPolynomial Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
set_option autoImplicit false
open NumberField MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
  {l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
variable (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l)

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet_letB {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) (b : Fin n → E) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.pushLet c γ (_root_.Formalism.L2.Pj.letB c σ i b) = _root_.Formalism.L2.Pj.letB c σ i (γ.mulVec b) := by sorry
