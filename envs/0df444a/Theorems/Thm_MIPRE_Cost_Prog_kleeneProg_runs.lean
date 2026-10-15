-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_kleeneProg_runs
-- name    : MIPRE.Cost.Prog.kleeneProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:27:58.585513+00:00
-- url     : https://prove2.me/theorems/39a41401-18f5-4749-be7c-d1ad95708600
-- title:
--   Forward run of the Kleene two-argument program $G$: from a run of $F(s(x,\mathrm{enc}(x)))$ on $v$, at explicit overhead
-- statement:
--   Programs of the ambient cost model (`Prog`) read their input as variable $0$ and are *closed* (`WellScoped 1`) when they read no other variable; $p(x) \Downarrow_t r$ (`p.Runs x r t`) says that $p$ run on the input $x$ halts with result $r$ at cost $t$ in the timed big-step semantics, and $\mathrm{size}(v)$ is the number of nodes of a datum $v$. Programs are encoded as data by their tree serialization $\mathrm{enc}(p)$, with $|p| := \mathrm{size}(\mathrm{enc}(p))$ (`esize`), and $s(p, d) = \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d, \mathtt{var}\ 0)\ \mathtt{in}\ p$ (`hardcode p d`) is the s-m-n map, running $p$ on the pair of the literal $d$ and its input. A *universal machine* $U = (u, P_U)$ (`UniversalMachine`) is a closed program $u$ with a polynomial $P_U \in \mathbb{N}[X]$ such that (i) whenever $c(v) \Downarrow_t r$ there is $t' \le P_U(|c| + \mathrm{size}(v) + t)$ with $u(\mathtt{cons}(\mathrm{enc}(c), v)) \Downarrow_{t'} r$ (`time_le`), and (ii) whenever $u(\mathtt{cons}(\mathrm{enc}(c), v)) \Downarrow_{t'} r$ there is $t$ with $c(v) \Downarrow_t r$ (`halts_of`). A *polynomial-time map on programs* $F$ (`PolyTimeFun Prog Prog`) is a function $F : \mathrm{Prog} \to \mathrm{Prog}$ with a closed program $\mathrm{code}_F$ and an explicit polynomial $T_F$ such that $\mathrm{code}_F(\mathrm{enc}(x)) \Downarrow_{t} \mathrm{enc}(F(x))$ for some $t \le T_F(|x|)$, for every $x$.
--
--   The two-argument program of the fixed-point construction is $G = \mathrm{kleeneProg}(u, F)$ (`kleeneProg`): on an input $\mathtt{cons}(\mathrm{enc}(x), v)$ it forms the pair $(\mathrm{enc}(x), \mathrm{enc}(x))$, applies the s-m-n program `smnProg` to obtain $\mathrm{enc}(s(x, \mathrm{enc}(x)))$, applies $\mathrm{code}_F$ to obtain $\mathrm{enc}(F(s(x, \mathrm{enc}(x))))$, pairs the result with $v$ and runs $u$ on that pair.
--
--   **Statement.** Let $U = (u, P_U)$ be a universal machine, $F$ a polynomial-time map on programs and $x$ a program, and write $e' := s(x, \mathrm{enc}(x))$. If $F(e')(v) \Downarrow_t r$, then there is a cost $T$ with $G(\mathtt{cons}(\mathrm{enc}(x), v)) \Downarrow_T r$ and
--
--   $$ T \;\le\; 6|x| + |e'| + T_F(|e'|) + 2\,|F(e')| + 2\,\mathrm{size}(v) + P_U\bigl(|F(e')| + \mathrm{size}(v) + t\bigr) + 57 . $$
--
--   This is the forward half of the fixed-point construction for the efficient Kleene recursion theorem (blueprint `lem:kleene`, [MNY, Lemma 2.3]): `kleeneFix_runs_of` instantiates it with $x := G$, for which $s(G, \mathrm{enc}(G))$ is the fixed point, and `efficient_fixed_point` uses it for the transfer of halting from $F(e)$ to $e$.
--
--   **Formalization Note**: The bound is the exact cost of the straight-line program up to the two bounded sub-runs: $6|x|$ for the copies of $\mathrm{enc}(x)$ read in the pairing, in passing the pair to the s-m-n program and inside it; $|e'|$ for passing $\mathrm{enc}(e')$ to $\mathrm{code}_F$; $T_F(|e'|)$ bounding that run; $2|F(e')| + 2\,\mathrm{size}(v)$ for the final pairing and for passing the pair to $u$; $P_U(\cdot)$ bounding the universal run; and $57$ units of rule costs and literals. No hypothesis is placed on $x$: the program whose description is hardcoded need not be closed.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Kleene.lean#L82-L112; internal lemma of the formalization of blueprint lem:kleene

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
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

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial

theorem MIPRE.Cost.Prog.kleeneProg_runs (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (x : Prog)
    {v r : Data} {t : ℕ} (h : (F (hardcode x (encode x))).Runs v r t) :
    ∃ T ≤ 6 * esize x + esize (hardcode x (encode x)) +
        F.timeBound.eval (esize (hardcode x (encode x))) +
        2 * esize (F (hardcode x (encode x))) + 2 * v.size +
        U.bound.eval (esize (F (hardcode x (encode x))) + v.size + t) + 57,
      (kleeneProg U.univ F).Runs (.cons (encode x) v) r T := by sorry
