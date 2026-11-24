-- Prove2me | Theorems.Thm_GlobalTheory_ShortDatumEq_pairL_cast
-- name    : GlobalTheory.ShortDatumEq.pairL_cast
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:13:18.187375+00:00
-- url     : https://prove2.me/theorems/fdc5ef17-7552-42b9-94b5-a76151768e6a
-- title:
--   Short Datum Eq: pair L cast
-- statement:
--   The Short Datum Eq construction uses the pair L cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdmissibleFalseIffFirstInvariant.lean#L37-L39

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdmissibleFalseIffFirstInvariant
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
open GlobalTheory GlobalTheory.ShortDatumEq
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem GlobalTheory.ShortDatumEq.pairL_cast {n : ℕ} (x0 x : Fin n → D.La) :
    ((pairL (l := l) x0 x : ℤ) : ZMod l.M) = pairing D l (cls l x0) (fun b => Submodule.Quotient.mk (x b)) := by sorry
