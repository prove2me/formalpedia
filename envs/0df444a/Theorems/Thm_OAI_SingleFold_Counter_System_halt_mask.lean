-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_halt_mask
-- name    : OAI.SingleFold.Counter.System.halt_mask
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:37:59.539267+00:00
-- url     : https://prove2.me/theorems/15c1ef78-862b-4171-b046-90fdf2bf7b8f
-- title:
--   The halting state is occupied exactly at the last step
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$, an input $d$, and a witness $v$ satisfying the counter system. In particular $B=2^w=4b$ with $2(1+|Q|+\sum_jd_j)<B$, $H=B^k=B\cdot\mathrm{last}$ with $k>0$, $\mathrm{mask}=\sum_{t<k}B^t$, the state indicators $\mathrm{state}_q$ are $\preceq\mathrm{mask}$ and sum to $\mathrm{mask}$, each branch splits its state, $\mathrm{state}_q=[q=\mathrm{start}]+B\cdot\mathrm{incoming}_q$, and every packed counter is $\preceq(2b-1)\mathrm{mask}$. Here $x\preceq y$ means binary digit domination, and $\mathrm{arc}(q,\beta)$ denotes the packed indicator of leaving $q$ along branch $\beta$. Then the packed indicator of the halting state equals the top power:
--   $$
--   \mathrm{state}_{\mathrm{halt}}=\mathrm{last}=B^{k-1} .
--   $$
--
--   The run reaches the halting state only at the last time step. So the witness encodes a halting computation of length $k-1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterMachine.lean#L264-L276

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

theorem OAI.SingleFold.Counter.System.halt_mask : v.state M.halt=v.last := by sorry
