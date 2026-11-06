-- Prove2me | Theorems.Thm_FromPrinted_Consequences_tm_of_colorings
-- name    : FromPrinted.Consequences.tm_of_colorings
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:43:06.066884+00:00
-- url     : https://prove2.me/theorems/1592250e-14fb-4895-9548-547559d0e1f8
-- title:
--   Consequences: tm of colorings
-- statement:
--   A Turing machine with finite alphabets that, started on the code of a graph G on n vertices,
--   halts with `post` of the number of proper colorings of G with k ≥ 3 colors within ⌊C·2^{δn}⌋ steps,
--   from the statement `StColoringsCounted` as a hypothesis: it simulates the machine of that statement
--   at δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L49-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Circuits.lean#L49-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_FromPrinted_Dom
import Definitions.Def_Consequences_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Circuits
set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount Turing

theorem FromPrinted.Consequences.tm_of_colorings (hCol : StColoringsCounted) (k : ℕ) (hk : 3 ≤ k) {δ : ℝ} (hδ : 0 < δ) (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      Outputs M (code G) (post (numColorings G k)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
