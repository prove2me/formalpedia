-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_searchProg_halts_of
-- name    : MIPRE.Cost.Prog.searchProg_halts_of
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:28.88237+00:00
-- url     : https://prove2.me/theorems/52bd11c1-10fc-48ca-91a6-8c9bbaeed2e3
-- title:
--   A halting run of the hardcoded search program yields the start-level string and a halting run of the semidecider
-- statement:
--   We work in the ambient cost model (programs `Prog` on binary-tree data, timed semantics, `Prog.Runs p x r t`; `Halts p x`: some run of $p$ on $x$ exists). A universal machine $U$ is a closed program $U.\mathrm{univ}$ that simulates any program $c$ on any $v$ with the same halting behavior and result (`UniversalMachine.time_le` and `UniversalMachine.halts_of`).
--
--   The compressibility criterion (Lin's criterion, blueprint `lem:compressible-criterion-nested`) adds a *search branch* to the self-referential decider of the recursive compression argument: at each level the decider tests, under a budget, whether a semidecision procedure $S$ accepts the string at the start level $m$ of the recursion. The program tested is the search program with its data hardcoded. For a universal program $\mathrm{univ}$ and a program $S$, $\mathrm{searchProg}(\mathrm{univ}, S)$ expects the pair of $d = \mathrm{encode}(((c', (e, (m, m))), m))$ and an (ignored) input: it runs $\mathrm{univ}$ on the first component of $d$, i.e. simulates $c'$ on the encoded triple $(e, (m, m))$ to obtain a value $x$ (the string at the start level), and then runs $S$ on the pair $\texttt{cons}(x, \mathrm{encode}(m))$. The s-m-n map $\mathrm{hardcode}(p, d) = \texttt{let\_}\,(\texttt{cons}\,(\texttt{const}\,d)\,(\texttt{var}\,0))\ p$ fixes $d$, so that $\mathrm{hardcode}(\mathrm{searchProg}(\mathrm{univ}, S), d)$ is a program to be run on the empty input `nil`.
--
--   Let $U$ be a universal machine, $S$ a closed program (well-scoped in one variable), $c', e$ programs, $m \in \mathbb{N}$, $r$ data and $T$ a cost, and suppose that $\mathrm{hardcode}(\mathrm{searchProg}(U.\mathrm{univ}, S), \mathrm{encode}(((c', (e, (m,m))), m)))$ on the input `nil` halts with $r$ at cost $T$. Then
--
--   $$ \exists\, x\ \exists\, t_x,\qquad c' \text{ on } \mathrm{encode}((e,(m,m))) \text{ halts with } x \text{ at cost } t_x\quad\wedge\quad S \text{ halts on } \texttt{cons}(x, \mathrm{encode}(m)). $$
--
--   This is the backward direction of the correctness of the search branch of the compressibility criterion's decider: if the search fires (the hardcoded search program halts within the budget), then the self-referential program $c'$ does produce a string $x$ at the start level and the semidecision procedure $S$ accepts $(x, m)$. In `compressibility_criterion_nested` this is combined with the determinism of evaluation (the $x$ produced is the decider's own output at the start level) and with the specification of $S$ to conclude that the start string lies outside $B_1(m)$.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.Prog.searchProg_halts_of`; the conclusion names the cost $t_x$ of the run of $c'$ but only the existence of a run of $S$ (`Halts S (cons x (encode m))`). Its proof is an inversion of the big-step derivation of the hardcoded program, which is possible because the semantics is deterministic and each syntactic form of program has exactly one applicable rule (two for `elim`, distinguished by the inspected value).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L372-L403; internal lemma of the formalization of blueprint lem:compressible-criterion-nested (the search branch of Lin's compressibility criterion, lem:compressible-criterion)

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

theorem MIPRE.Cost.Prog.searchProg_halts_of (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {r : Data} {T : ℕ}
    (h : (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T) :
    ∃ x tx, c'.Runs (encode (e, (m, m))) x tx ∧ Halts S (.cons x (encode m)) := by sorry
