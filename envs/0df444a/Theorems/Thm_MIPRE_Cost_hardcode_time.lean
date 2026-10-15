-- Prove2me | Theorems.Thm_MIPRE_Cost_hardcode_time
-- name    : MIPRE.Cost.hardcode_time
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:11.487176+00:00
-- url     : https://prove2.me/theorems/739338f1-5b0a-43c4-874b-a88d4820fce6
-- title:
--   Efficient s-m-n, forward direction: a run of $p$ on $(d,x)$ yields a run of $s(p,d)$ on $x$ at additive linear overhead
-- statement:
--   Programs of the ambient cost model (`Prog`) take their input as variable $0$ of a de Bruijn environment; a program $p$ is *closed* (`p.WellScoped 1`) if it reads no variable other than its input. Data are binary trees, $\mathrm{size}$ being the number of nodes. Write $p(x) \Downarrow_t r$ (`p.Runs x r t`) for "$p$ run on the single input $x$ halts with result $r$ at cost $t$" in the timed big-step semantics, in which each evaluation rule costs one unit and reading a variable or a literal costs the size of the value in addition. The s-m-n map of the model is
--
--   $$ s(p, d) \;:=\; \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d,\ \mathtt{var}\ 0)\ \mathtt{in}\ p \qquad\text{(`hardcode p d`)}, $$
--
--   the program which pairs the literal $d$ with its own input and runs $p$ on the pair.
--
--   **Statement.** Let $p$ be a closed program, $d, x, r$ data and $t \in \mathbb{N}$. If $p(\mathtt{cons}(d, x)) \Downarrow_t r$, then
--
--   $$ s(p,d)(x) \;\Downarrow_{\,t + \mathrm{size}(d) + \mathrm{size}(x) + 3}\; r . $$
--
--   This is one half of the functional equation $\varphi_{s(p,d)}(x) = \varphi_p(d, x)$ of the efficient s-m-n theorem (blueprint `lem:smn`, [MNY, Lemma 2.2]), with the forward time transfer. It is used wherever a program with a hardcoded argument must be shown to run fast: the Kleene fixed point (`kleeneFix_runs_of`, `efficient_fixed_point`), succinctness of the hardcoded bit-query program (`isSuccinctDesc_hardcode`), the compiler from Mathlib's codes (`exists_compile`), and the time transfer of the self-referential decider in the recursive compression lemma.
--
--   **Formalization Note**: The conclusion is a run with an *exact* cost, not an upper bound: $\mathrm{size}(d)$ for building the literal, $\mathrm{size}(x) + 1$ for reading the input, one unit for the pairing node and one for the `let_`. [MNY] only asks the runtimes of $e$ and $s(e,x)$ to be polynomially related. The closedness hypothesis on $p$ is what allows the run of $p$ to be transported into the environment $[\mathtt{cons}(d,x), x]$ in which the body of the `let_` executes: the original input remains visible below the pair, but a closed program never reads it.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean#L71-L76; blueprint lem:smn, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.2

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.hardcode_time {p : Prog} (hp : p.WellScoped 1) {d x r : Data} {t : ℕ}
    (h : p.Runs (.cons d x) r t) : (hardcode p d).Runs x r (t + d.size + x.size + 3) := by sorry
