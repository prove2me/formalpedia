-- Prove2me | Theorems.Thm_MIPRE_Cost_efficient_fixed_point
-- name    : MIPRE.Cost.efficient_fixed_point
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:18.720616+00:00
-- url     : https://prove2.me/theorems/ffd0fe4f-5869-4b83-8b2c-dec29abf539a
-- title:
--   Efficient Kleene recursion theorem: a polynomial-time map on programs has a fixed point, with polynomial time transfer
-- statement:
--   Programs of the ambient cost model (`Prog`) read their input as variable $0$; a program $p$ is *closed* (`p.WellScoped 1`) if it reads no other variable; $p(v) \Downarrow_t r$ (`p.Runs v r t`) says that $p$ run on the input $v$ halts with result $r$ at cost $t$ in the timed big-step semantics, and $\mathrm{size}(v)$ is the number of nodes of the datum $v$. Programs are encoded as data by their tree serialization $\mathrm{enc}(p)$, with $|p| := \mathrm{size}(\mathrm{enc}(p))$. A *polynomial-time map on programs* $F$ (`PolyTimeFun Prog Prog`) is a function $F : \mathrm{Prog} \to \mathrm{Prog}$ together with a closed program computing $\mathrm{enc}(F(x))$ from $\mathrm{enc}(x)$ within an explicit polynomial bound $T_F(|x|)$.
--
--   **Statement.** For every polynomial-time map on programs $F$ there exist a program $e$ and a polynomial $P \in \mathbb{N}[X]$ such that
--
--   1. $e$ is closed;
--   2. for all $v, r$: $\;\exists t,\ e(v) \Downarrow_t r \iff \exists t,\ F(e)(v) \Downarrow_t r$, that is, $e$ and $F(e)$ compute the same partial function, $\varphi_e = \varphi_{F(e)}$;
--   3. for all $v, r, t$: if $F(e)(v) \Downarrow_t r$, then there is $t' \le P(\mathrm{size}(v) + t)$ with $e(v) \Downarrow_{t'} r$.
--
--   $$ \exists\, e, P:\quad e \text{ closed},\qquad \varphi_e = \varphi_{F(e)},\qquad F(e)(v) \Downarrow_t r \;\Longrightarrow\; \exists t' \le P(\mathrm{size}(v) + t),\ e(v) \Downarrow_{t'} r . $$
--
--   This is the efficient Kleene recursion theorem (blueprint `lem:kleene`, [MNY, Lemma 2.3]), the last piece of the efficient computability toolkit after the universal machine (`lem:universal-tm`) and the s-m-n theorem (`lem:smn`). The recursive compression lemma and the compressibility criterion apply it to the map $c' \mapsto s(\mathrm{code}_{\mathrm{dec}}, \mathrm{enc}(c'))$ to obtain the self-referential decider $c$ that computes $\mathrm{dec}(c, \cdot)$; clause 3 is what makes $c$ a polynomial-time, hence succinct, description at every level of the recursion.
--
--   **Formalization Note**: The fixed point is the explicit program `kleeneFix U F` $= s(G, \mathrm{enc}(G))$ for the two-argument program $G$ (`kleeneProg`), built from a universal machine $U = (u, P_U)$ obtained from `exists_efficient_universal`, and the polynomial is $P = P_U(X + |F(e)|) + 3X + \mathrm{kleeneOverhead}(U, F)$ with the constant of `kleeneFix_runs_of`. The map $F$ acts on programs rather than on bit strings as in the paper, programs being their own descriptions in this model. Departure from [MNY, Lemma 2.3], recorded in the source: the paper states the runtimes of $e$ and $F(e)$ as polynomially *equivalent*; only the direction "runs of $F(e)$ bound runs of $e$" is used by the recursive compression argument, and only it follows from the time-transfer clause of the universal machine. The converse would require a universal machine that is never faster than the simulated program, a clause deliberately omitted from `UniversalMachine` to keep that obligation minimal.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Kleene.lean#L205-L232; blueprint lem:kleene, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 2.3

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
open Polynomial

theorem MIPRE.Cost.efficient_fixed_point (F : PolyTimeFun Prog Prog) :
    ∃ (e : Prog) (p : Polynomial ℕ),
      e.WellScoped 1 ∧
      (∀ v r, (∃ t, e.Runs v r t) ↔ ∃ t, (F e).Runs v r t) ∧
      ∀ v r t, (F e).Runs v r t → ∃ t' ≤ p.eval (v.size + t), e.Runs v r t' := by sorry
