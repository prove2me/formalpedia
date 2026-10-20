-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_selected_digit
-- name    : OAI.SingleFold.Counter.System.selected_digit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:38:32.436098+00:00
-- url     : https://prove2.me/theorems/47907774-2eb9-4a91-b3a2-3c98aa9e17f0
-- title:
--   Digits of a sum of selected arcs add without carries
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$, an input $d$, and a witness $v$ satisfying the counter system. In particular $B=2^w=4b$ with $2(1+|Q|+\sum_jd_j)<B$, $H=B^k=B\cdot\mathrm{last}$ with $k>0$, $\mathrm{mask}=\sum_{t<k}B^t$, the state indicators $\mathrm{state}_q$ are $\preceq\mathrm{mask}$ and sum to $\mathrm{mask}$, each branch splits its state, $\mathrm{state}_q=[q=\mathrm{start}]+B\cdot\mathrm{incoming}_q$, and every packed counter is $\preceq(2b-1)\mathrm{mask}$. Here $x\preceq y$ means binary digit domination, and $\mathrm{arc}(q,\beta)$ denotes the packed indicator of leaving $q$ along branch $\beta$. For a predicate $P$ on arcs let $\mathrm{sel}(P)=\sum_{q,\beta:\,P(q,\beta)}\mathrm{arc}(q,\beta)$. Then for $t<k$
--   $$
--   \mathrm{digit}_B\bigl(\mathrm{sel}(P),t\bigr)=\sum_{q,\beta:\,P(q,\beta)}\mathrm{digit}_B\bigl(\mathrm{arc}(q,\beta),t\bigr) .
--   $$
--
--   At each time step at most one arc is used, so the selected sum has digit $1$ exactly when a selected arc is taken.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterMachine.lean#L321-L337

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine

open OAI OAI.SingleFold OAI.SingleFold.Counter OAI.SingleFold.Counter.System
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
variable (h : System M d v)
include h

theorem OAI.SingleFold.Counter.System.selected_digit (P : Q → Bool → Prop) [DecidableRel P] (t : ℕ) (ht : t < v.k) :
    digit v.B (selected (M:=M) (v:=v) P) t=∑q,∑b : Bool,if P q b then digit v.B (arc M v q b) t else 0 := by sorry
