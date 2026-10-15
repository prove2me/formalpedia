-- Prove2me | Theorems.Thm_MIPRE_Cost_hardcode_time_rev
-- name    : MIPRE.Cost.hardcode_time_rev
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:29:22.06186+00:00
-- url     : https://prove2.me/theorems/47bee20e-a916-4611-956e-058033e889cc
-- title:
--   Efficient s-m-n, backward direction: a run of $s(p,d)$ on $x$ restricts to a run of $p$ on $(d,x)$ of no larger cost
-- statement:
--   Programs of the ambient cost model (`Prog`) take their input as variable $0$ of a de Bruijn environment; a program $p$ is *closed* (`p.WellScoped 1`) if it reads no variable other than its input. Data are binary trees, $\mathrm{size}$ being the number of nodes. Write $p(x) \Downarrow_t r$ (`p.Runs x r t`) for "$p$ run on the single input $x$ halts with result $r$ at cost $t$" in the timed big-step semantics, in which each evaluation rule costs one unit and reading a variable or a literal costs the size of the value in addition. The s-m-n map of the model is
--
--   $$ s(p, d) \;:=\; \mathtt{let}\ \mathtt{cons}(\mathtt{const}\ d,\ \mathtt{var}\ 0)\ \mathtt{in}\ p \qquad\text{(`hardcode p d`)}, $$
--
--   the program which pairs the literal $d$ with its own input and runs $p$ on the pair.
--
--   **Statement.** Let $p$ be a closed program, $d, x, r$ data and $t \in \mathbb{N}$. If $s(p,d)(x) \Downarrow_t r$, then there is a cost $t' \le t$ with
--
--   $$ p(\mathtt{cons}(d, x)) \;\Downarrow_{t'}\; r . $$
--
--   This is the other half of the functional equation $\varphi_{s(p,d)}(x) = \varphi_p(d,x)$ of the efficient s-m-n theorem (blueprint `lem:smn`, [MNY, Lemma 2.2]): hardcoding creates no halting behaviour that $p$ does not have, and does not lower the cost. It is used to invert runs of hardcoded programs: in the backward direction of `kleeneFix_halts_iff` inside the Kleene fixed-point theorem `efficient_fixed_point`, in the halting equivalence of the compiler `exists_compile`, and to invert the runs of the search program of the compressibility criterion.
--
--   **Formalization Note**: By determinism of the semantics the cost is in fact $t' = t - \mathrm{size}(d) - \mathrm{size}(x) - 3$, but the statement records only $t' \le t$, which is what its consumers need. The closedness hypothesis is used to strip the extra environment entry $x$ from the run of the body; without it the body could read the original input and the restriction would fail.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Toolkit.lean#L78-L87; blueprint lem:smn, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.2

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

theorem MIPRE.Cost.hardcode_time_rev {p : Prog} (hp : p.WellScoped 1) {d x r : Data} {t : ℕ}
    (h : (hardcode p d).Runs x r t) : ∃ t' ≤ t, p.Runs (.cons d x) r t' := by sorry
