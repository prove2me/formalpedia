-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnusedSlot36_ordVal_smul
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.ordVal_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:22:16.506315+00:00
-- url     : https://prove2.me/theorems/269a4577-5ec5-4481-9df4-5115afbb64d6
-- title:
--   Unused Slot36: ord Val smul
-- statement:
--   The Unused Slot36 construction uses the ord Val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean#L84-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean#L84-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_OrderValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)
variable {Xo c}
variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
variable {Xo c U}

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.ordVal_smul {o : Rul Xo c → EReal} (ho : o ∈ ordVal Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    o (a • f) = o f := by sorry
