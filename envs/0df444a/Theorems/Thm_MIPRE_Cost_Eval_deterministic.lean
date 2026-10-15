-- Prove2me | Theorems.Thm_MIPRE_Cost_Eval_deterministic
-- name    : MIPRE.Cost.Eval.deterministic
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:14.316703+00:00
-- url     : https://prove2.me/theorems/49db57a3-6102-4481-8b7b-02ce75007b88
-- title:
--   Determinism of the timed big-step semantics: a run has a unique result and a unique cost
-- statement:
--   Let $\mathsf{Data}$ be the type of binary trees (the values of the ambient cost model, built from $\mathsf{nil}$ and $\mathsf{cons}$), let $\mathsf{Prog}$ be the type of programs of the ambient first-order language with de Bruijn variables, and let an *environment* $\rho$ be a list of values (variable $i$ reads the $i$-th entry, and $\mathsf{nil}$ beyond the end of the list). The timed big-step semantics is the inductively defined relation $\mathsf{Eval}\;\rho\;p\;r\;t$, read "in environment $\rho$ the program $p$ halts with result $r$ at cost $t \in \mathbb{N}$". It charges one unit per evaluation rule, except that reading a variable costs $1 + \mathrm{size}$ of the value read and a literal $\mathsf{const}\,d$ costs $\mathrm{size}(d)$.
--
--   Let $\rho$ be an environment, $p$ a program, $r, r'$ values and $t, t'$ natural numbers. If both $\mathsf{Eval}\;\rho\;p\;r\;t$ and $\mathsf{Eval}\;\rho\;p\;r'\;t'$ hold, then
--   $$ r = r' \quad\text{and}\quad t = t'. $$
--
--   In words: the semantics is a partial function of the environment and the program, in both its result and its cost. This is the lemma that lets a run of a program be "read back": whenever a derivation is inverted (a run of the self-interpreter, of the s-m-n program, of a clocked simulation), the sub-run that one has constructed by hand must coincide with the one in the hypothesis. It also makes the budgeted result `evalWithin` (and hence `clockedResult`) well defined.
--
--   **Formalization Note**: The statement is about the relation `MIPRE.Cost.Eval` of `Cost/Basic.lean`; `Env` is `List Data`, lookup is `Env.get` (total, returning $\mathsf{nil}$ out of range), and there is no well-scopedness hypothesis on $p$. Determinism includes the cost, so the cost $t$ of a halting run is a function of $(\rho, p)$; `Prog.Runs p v r t` is the special case $\rho = [v]$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Basic.lean#L274-L323; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Eval

theorem MIPRE.Cost.Eval.deterministic {env : Env} {p : Prog} {r r' : Data} {t t' : ℕ}
    (h : Eval env p r t) (h' : Eval env p r' t') : r = r' ∧ t = t' := by sorry
