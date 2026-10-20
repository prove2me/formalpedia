-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_System_counter_info
-- name    : OAI.SingleFold.Counter.System.counter_info
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:37:26.141147+00:00
-- url     : https://prove2.me/theorems/8b250c45-3741-4ce6-8a46-2c1441fbc497
-- title:
--   Packed counters have the right length and small digits
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$, an input $d$, and a witness $v$ satisfying the counter system. In particular $B=2^w=4b$ with $2(1+|Q|+\sum_jd_j)<B$, $H=B^k=B\cdot\mathrm{last}$ with $k>0$, $\mathrm{mask}=\sum_{t<k}B^t$, the state indicators $\mathrm{state}_q$ are $\preceq\mathrm{mask}$ and sum to $\mathrm{mask}$, each branch splits its state, $\mathrm{state}_q=[q=\mathrm{start}]+B\cdot\mathrm{incoming}_q$, and every packed counter is $\preceq(2b-1)\mathrm{mask}$. Here $x\preceq y$ means binary digit domination, and $\mathrm{arc}(q,\beta)$ denotes the packed indicator of leaving $q$ along branch $\beta$. Then for every counter $j$, including the clock,
--   $$
--   \mathrm{counter}_j<B^k\qquad\text{and}\qquad\mathrm{digit}_B(\mathrm{counter}_j,t)<2b\ \ (t<k) .
--   $$
--
--   Each packed counter is a sequence of $k$ values, each below $2b=B/2$. So sums of two digits never carry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterMachine.lean#L182-L193

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

theorem OAI.SingleFold.Counter.System.counter_info (j : Option J) : v.counter j < v.B^v.k ∧ ∀t < v.k,digit v.B (v.counter j) t < 2*v.b := by sorry
