-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnusedSlot36_NoCommonZero_at
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero.at
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:22.561192+00:00
-- url     : https://prove2.me/theorems/851cdc87-c9ee-4a39-a593-d6b539ae6cb8
-- title:
--   No Common Zero: at
-- statement:
--   The No Common Zero construction uses the at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/OrderValuation.lean#L69-L78

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36.NoCommonZero.at {κ : Type} {w : κ → Rul Xo c} (h : NoCommonZero w) (la : HeightOneSpectrum (𝓞 c.F)) :
    NoCommonZeroAt la w := by sorry
