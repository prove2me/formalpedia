-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_fixBody_runs
-- name    : MIPRE.Cost.Prog.fixBody_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:08.07133+00:00
-- url     : https://prove2.me/theorems/533cd753-e47f-4aca-9c1d-15aa5d5f10dc
-- title:
--   The body of the translated `fix` loop dispatches on the head of the output of $f$ as the loop flag
-- statement:
--   Mathlib's `Turing.ToPartrec.Code` is a small first-order language on lists of natural numbers, with constructors $\mathtt{zero'}$, $\mathtt{succ}$, $\mathtt{tail}$, $\mathtt{cons}\,f\,fs$, $\mathtt{comp}\,f\,g$, $\mathtt{case}\,f\,g$ and $\mathtt{fix}\,f$, in which every partial recursive function is computable. The translation $\mathrm{ofCode} : \mathrm{Code} \to \mathrm{Prog}$ (`Prog.ofCode`) maps it construct by construct into the language of the ambient cost model: lists of naturals are encoded as $\mathtt{cons}$-chains of unary numerals $\mathrm{encL}(v)$ (`encL`; the numeral $\bar k$ is the list of $k$ copies of $\mathtt{nil}$), $\mathtt{zero'}$ prepends $\mathtt{nil}$, $\mathtt{succ}$ and $\mathtt{tail}$ are `elim`s on the input, $\mathtt{cons}$ and $\mathtt{comp}$ are `let_` binders with calls of the translated subprograms, $\mathtt{case}$ is a double `elim` on the head of the input, and $\mathtt{fix}$ is a `loop` whose body runs the translated $f$ and dispatches on the head of its result (`fixBody`). Write $p(x) \Downarrow_t r$ for a run of the program $p$ on the input $x$ with result $r$ at cost $t$, and $\rho \vdash p \Downarrow_s r$ for a run in the environment $\rho$ (`Eval`). For a program $pf$, the loop body is
--
--   $$ \mathrm{fixBody}(pf) = \mathtt{let}\ (\mathtt{callVar}\ 0\ pf)\ \mathtt{in}\ \mathtt{elim}\ 0\ \bigl(\mathtt{cons}(\mathtt{nil},\mathtt{nil})\bigr)\ \Bigl(\mathtt{elim}\ 0\ \bigl(\mathtt{cons}(\mathtt{nil}, \mathtt{var}\ 1)\bigr)\ \bigl(\mathtt{cons}(\mathtt{cons}(\mathtt{nil},\mathtt{nil}), \mathtt{var}\ 3)\bigr)\Bigr), $$
--
--   which runs $pf$ on the loop state and inspects the head of the result. The loop protocol of the model is that a body value $\mathtt{cons}(\mathtt{nil}, w)$ stops the loop with result $w$, while $\mathtt{cons}(\mathtt{cons}(\cdot,\cdot), w)$ continues with the state $w$. The intended body value is (`fixFlag`)
--
--   $$ \mathrm{fixFlag}([]) = \mathtt{cons}(\mathtt{nil}, \mathtt{nil}),\qquad \mathrm{fixFlag}(0 :: w) = \mathtt{cons}(\mathtt{nil}, \mathrm{encL}(w)),\qquad \mathrm{fixFlag}((n+1) :: w) = \mathtt{cons}(\mathtt{cons}(\mathtt{nil},\mathtt{nil}), \mathrm{encL}(w)), $$
--
--   mirroring Mathlib's semantics of $\mathtt{fix}\,f$: stop with $[]$ if $f$ returns $[]$, stop with $w$ if it returns $0 :: w$, and iterate from $w$ if it returns $(n+1) :: w$.
--
--   **Statement.** Let $pf$ be a closed program and $v, fv$ lists of naturals such that $pf(\mathrm{encL}(v)) \Downarrow_t \mathrm{encL}(fv)$ for some $t$. Then there is a cost $s$ with
--
--   $$ [\mathrm{encL}(v)] \vdash \mathrm{fixBody}(pf) \Downarrow_s \mathrm{fixFlag}(fv) . $$
--
--   This is the single-iteration lemma for the `fix` case of both correctness directions of the translation: `ofCode_sound` uses it to build the run of the loop, and `ofCode_complete` uses it, with determinism, to show that any run of the body returns a `fixFlag` value. It serves blueprint `lem:halting-form` through `exists_compile`.
--
--   **Formalization Note**: No cost is tracked ($s$ is existential): the translation from Mathlib's codes is a computability-only bridge. The encoding $\mathrm{encL}$ uses unary numerals, so that the head test is a single `elim`; the environment is the singleton $[\mathrm{encL}(v)]$, the loop state being variable $0$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/FromPartrec.lean#L105-L118; internal lemma of the formalization of blueprint lem:halting-form (the bridge from Mathlib's partial recursive functions into the model)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Turing.ToPartrec (Code)

theorem MIPRE.Cost.Prog.fixBody_runs {pf : Prog} (hpf : pf.WellScoped 1) (v fv : List ℕ) {t : ℕ}
    (h : pf.Runs (encL v) (encL fv) t) :
    ∃ s, Eval [encL v] (fixBody pf) (fixFlag fv) s := by sorry
