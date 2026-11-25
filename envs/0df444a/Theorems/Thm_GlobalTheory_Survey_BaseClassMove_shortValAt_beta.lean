-- Prove2me | Theorems.Thm_GlobalTheory_Survey_BaseClassMove_shortValAt_beta
-- name    : GlobalTheory.Survey.BaseClassMove.shortValAt_beta
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:19.307697+00:00
-- url     : https://prove2.me/theorems/90ac1db0-e582-4495-a19b-274778f066ab
-- title:
--   Base Class Move: short Val At beta
-- statement:
--   The Base Class Move construction uses the short Val At beta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BaseClassMove.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/BaseClassMove.lean#L41-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BaseClassMove
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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.BaseClassMove
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

theorem GlobalTheory.Survey.BaseClassMove.shortValAt_beta (nab : NabV Xo c) {n : ℕ} (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (β : c.F)
    (hβ : β ≠ 0) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) :
    ShortValAt Xo c nab w Λ β N P y v ↔ ShortValAt Xo c nab w Λ 1 N P y (algebraMap c.F S β * v) := by sorry
