-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_searchProg_runs
-- name    : MIPRE.Cost.Prog.searchProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:39.731808+00:00
-- url     : https://prove2.me/theorems/4342da49-7184-452f-a3ea-b1eff467ab3d
-- title:
--   The hardcoded search program halts once the start-level string is produced and the semidecider accepts it
-- statement:
--   We work in the ambient cost model (programs `Prog` on binary-tree data, timed semantics, `Prog.Runs p x r t`: the program $p$ on the input $x$ halts with $r$ at cost $t$). A universal machine $U$ (`UniversalMachine`) is a closed program $U.\mathrm{univ}$ with a polynomial overhead such that every run of a program $c$ on $v$ with result $r$ yields a run of $U.\mathrm{univ}$ on the pair $(\mathrm{encode}(c), v)$ with the same result, and conversely $U.\mathrm{univ}$ halts on $(\mathrm{encode}(c), v)$ only if $c$ halts on $v$, with the same result.
--
--   The compressibility criterion (Lin's criterion, blueprint `lem:compressible-criterion-nested`) adds a *search branch* to the self-referential decider of the recursive compression argument: at each level the decider tests, under a budget, whether a semidecision procedure $S$ accepts the string at the start level $m$ of the recursion. The program tested is the search program with its data hardcoded. For a universal program $\mathrm{univ}$ and a program $S$, $\mathrm{searchProg}(\mathrm{univ}, S)$ expects the pair of $d = \mathrm{encode}(((c', (e, (m, m))), m))$ and an (ignored) input: it runs $\mathrm{univ}$ on the first component of $d$, i.e. simulates $c'$ on the encoded triple $(e, (m, m))$ to obtain a value $x$ (the string at the start level), and then runs $S$ on the pair $\texttt{cons}(x, \mathrm{encode}(m))$. The s-m-n map $\mathrm{hardcode}(p, d) = \texttt{let\_}\,(\texttt{cons}\,(\texttt{const}\,d)\,(\texttt{var}\,0))\ p$ fixes $d$, so that $\mathrm{hardcode}(\mathrm{searchProg}(\mathrm{univ}, S), d)$ is a program to be run on the empty input `nil`.
--
--   Let $U$ be a universal machine, $S$ a closed program (well-scoped in one variable), $c', e$ programs, $m \in \mathbb{N}$, and $x, r$ data. Suppose that $c'$ on $\mathrm{encode}((e, (m, m)))$ halts with $x$ (at some cost $t_x$) and that $S$ on $\texttt{cons}(x, \mathrm{encode}(m))$ halts with $r$ (at some cost $t_s$). Then
--
--   $$ \exists T,\qquad \mathrm{hardcode}\bigl(\mathrm{searchProg}(U.\mathrm{univ}, S),\ \mathrm{encode}(((c', (e, (m,m))), m))\bigr)\ \text{on the input `nil` halts with } r \text{ at cost } T. $$
--
--   This is the forward direction of the correctness of the search branch; with its converse `searchProg_halts_of` it shows that the search branch of the decider fires exactly when $S$ halts on the string at the start level, which is what the proof of `compressibility_criterion_nested` uses (the search eventually fires if the start string lies outside the class recognized by $S$).
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Prog.searchProg_runs`; the triple $(e, (m, m))$ carries the start level $m$ twice because the decider's input is $(c', (e, (m, n)))$ with $m$ the start level and $n$ the current level, and the search is about the string at $n = m$. The semidecider $S$ receives the pair $\texttt{cons}(x, \mathrm{encode}(m))$, in the per-level form of the criterion where $S$ halts on $(x, n)$ iff $x \notin B_1(n)$. No cost bound is claimed (only the existence of a halting run), since the decider tests halting within a budget that is then taken large enough.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L348-L370; internal lemma of the formalization of blueprint lem:compressible-criterion-nested (the search branch of Lin's compressibility criterion, lem:compressible-criterion)

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
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
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial

theorem MIPRE.Cost.Prog.searchProg_runs (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {x r : Data} {tx ts : ℕ}
    (hx : c'.Runs (encode (e, (m, m))) x tx) (hSr : S.Runs (.cons x (encode m)) r ts) :
    ∃ T, (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T := by sorry
