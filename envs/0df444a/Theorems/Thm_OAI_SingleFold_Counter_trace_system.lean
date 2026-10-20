-- Prove2me | Theorems.Thm_OAI_SingleFold_Counter_trace_system
-- name    : OAI.SingleFold.Counter.trace_system
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:48:19.355863+00:00
-- url     : https://prove2.me/theorems/a0bdd8a7-b207-4a18-b122-8a54ba99bfd9
-- title:
--   The packed trace of a halting run solves the counter system
-- statement:
--   Consider a counter machine with finite sets of states $Q$ and counters $J$ (each instruction halts, increments a counter, or tests a counter and decrements it if nonzero), an input $d\in\mathbb{N}^J$, and a witness $v$ satisfying the counter system: base $B=2^w=4b$, length $k>0$, packed state indicators $\mathrm{state}_q$, packed branch indicators $\mathrm{zero}_q,\mathrm{dec}_q$ of test states, packed counter histories $\mathrm{counter}_j$, and the polynomial and binary-domination conditions linking them. Write $\mathrm{digit}(x,t)=\lfloor x/B^t\rfloor\bmod B$, and let $\mathrm{inc}_j,\mathrm{dec}_j$ be the sums of the arc indicators that increment, resp. decrement, counter $j$. Suppose the machine halts on $d$ at time $T$, and $B=2^w$ with $w>0$, $B=4b$, $b>0$, and
--   $$
--   2(C(d)+T)<B,\qquad b\le C(d)+T,
--   $$
--   where $C(d)=1+|Q|+\sum_jd_j$. Then the trace witness, which packs the configurations of the run at times $0,\dots,T$ in base $B$, satisfies the counter system.
--
--   This is the completeness of the arithmetization: every halting run has a witness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/CounterBounds.lean#L254-L346

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
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds

open OAI OAI.SingleFold OAI.SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]

theorem OAI.SingleFold.Counter.trace_system (M : Machine Q J) (d : J → ℕ) (B w b T : ℕ)
    (hT : HaltsAt M d T) (hB : B=2^w) (hw : 0 < w) (hb : 0 < b)
    (hbase : B=4*b) (hlarge : 2*(baseC Q d+T) < B) (hsmall : b ≤ baseC Q d+T) :
    System M d (trace M d B w b T) := by sorry
