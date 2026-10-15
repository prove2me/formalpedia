-- Prove2me | Theorems.Thm_MIPRE_Cost_exists_efficient_universal
-- name    : MIPRE.Cost.exists_efficient_universal
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:51.761598+00:00
-- url     : https://prove2.me/theorems/7442bc35-0466-471f-8209-8c855b06851f
-- title:
--   Existence of an efficient universal machine for the ambient cost model
-- statement:
--   Fix the ambient cost model of the formalization: programs $c \in \mathsf{Prog}$ run on values $v \in \mathsf{Data}$ (binary trees), $\mathsf{Eval}\;[v]\;c\;r\;t$ (in Lean `c.Runs v r t`) says that $c$ on input $v$ halts with result $r$ at cost $t \in \mathbb{N}$, so that $\varphi_c(v) = r$ for the unique such $r$, and $\mathrm{runtime}(c, v) = t$; every program is encoded as a value $\lceil c\rceil$ (`encode c`, the tree serialization `Prog.toData`) of size $|c| = \mathrm{esize}(c)$, and pairs are encoded by $\mathsf{cons}$. A program is *closed* (`WellScoped 1`) when it reads only its input, variable $0$.
--
--   An *efficient universal machine* (`UniversalMachine`) is a structure consisting of a closed program $u$ and a polynomial $p \in \mathbb{N}[X]$ such that:
--   1. (simulation, with time bound) for every program $c$, input $v$, result $r$ and cost $t$ with $\mathsf{Eval}\;[v]\;c\;r\;t$, there is a cost $t' \le p\bigl(|c| + |v| + t\bigr)$ with $\mathsf{Eval}\;[\mathsf{cons}\,\lceil c\rceil\,v]\;u\;r\;t'$;
--   2. (no spurious halting) for every $c$, $v$, $r$ and $t'$ with $\mathsf{Eval}\;[\mathsf{cons}\,\lceil c\rceil\,v]\;u\;r\;t'$, there is a cost $t$ with $\mathsf{Eval}\;[v]\;c\;r\;t$.
--
--   The theorem states that such a machine exists:
--   $$ \mathsf{Nonempty}\;\mathtt{UniversalMachine} , $$
--   that is, there are a closed program $u$ and a polynomial $p$ with $\varphi_u(\lceil c\rceil, v) = \varphi_c(v)$ for all $c, v$ (both sides defined or undefined together, with the same value) and $\mathrm{runtime}(u, (\lceil c\rceil, v)) \le p\bigl(|c| + |v| + \mathrm{runtime}(c, v)\bigr)$ whenever the right-hand side is defined.
--
--   This is blueprint `lem:universal-tm` (the efficient universal Turing machine, [MNY, Lemma 2.1]), the first result of the efficient computability toolkit. It is the universal machine used by the efficient Kleene recursion theorem (`efficient_fixed_point`, blueprint `lem:kleene`) and, through it, by the recursive compression lemma; the compression pipeline's deciders use its clocked companion `exists_clocked_universal`.
--
--   **Formalization Note**: The blueprint states the bound with a polynomial in three arguments $|e|, |x|, \mathrm{runtime}(e,x)$; the Lean uses a single polynomial in their sum, which is equivalent. The structure is stated as data (program and polynomial as fields) rather than as an existential so that downstream definitions can name them; the theorem only asserts that the type is inhabited, and its witness is the self-interpreter `selfUniversal` of `Cost/Universal.lean` (program `univProg`, polynomial `univPoly` with $\mathtt{univPoly}(X) = (3X+1)(\mathtt{interpBodyBound}(\mathtt{sigmaFun}\,X) + 1) + 2X + 11$). The input is the pair $(\lceil c\rceil, v)$ encoded as $\mathsf{cons}\,\lceil c\rceil\,v$, and the sizes $|c|, |v|$ are node counts of the encodings, which are the bit-lengths of their preorder serializations.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Universal.lean#L1537-L1538; blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.1

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

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.exists_efficient_universal : Nonempty UniversalMachine := by sorry
