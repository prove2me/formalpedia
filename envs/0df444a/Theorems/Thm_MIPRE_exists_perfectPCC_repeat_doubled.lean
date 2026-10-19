-- Prove2me | Theorems.Thm_MIPRE_exists_perfectPCC_repeat_doubled
-- name    : MIPRE.exists_perfectPCC_repeat_doubled
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:44:01.038054+00:00
-- url     : https://prove2.me/theorems/ac1cc311-9108-48a0-a3ca-9978e42d74a0
-- title:
--   Game-level completeness of direct repetition: perfect PCC strategies of the doubled game
-- statement:
--   Let $G$ be a game whose two players share the finite question alphabet $X$ and the finite answer alphabet $A$: a probability distribution $\mu$ on $X \times X$ and a decision predicate $D$. Its doubled game $G^{\mathrm{dbl}}$ is the synchronous game with question alphabet $\{0,1\} \times X$ and answer alphabet $A$ in which $\mu^{\mathrm{dbl}}((0,x),(1,y)) = \mu(x,y)$ and $D^{\mathrm{dbl}}((0,x),(1,y),a,b) = D(x,y,a,b)$, while every other pair of tagged questions has weight $0$ and is rejected. A synchronous strategy $S = (d, M)$ for a synchronous game is a dimension $d > 0$ and a projective measurement $\{M^p_a\}_{a}$ on $\mathbb{C}^d$ for each question $p$; its value is $\sum_{p,q,a,b} \mu(p,q)\,D(p,q,a,b)\,\mathrm{Tr}(M^p_a M^q_b)/d$, and it is PCC when $M^p_a M^q_b = M^q_b M^p_a$ for all $a, b$ whenever $\mu(p,q) > 0$. For $k \in \mathbb{N}$, $G^{k}$ is the $k$-fold direct repetition of $G$ (alphabets $X^k$, $A^k$, product distribution, conjunction of the coordinate predicates).
--
--   For every $k \in \mathbb{N}$, if the doubled game of $G$ has a PCC synchronous strategy of value $1$, then so does the doubled game of $G^{k}$:
--
--   $$\bigl(\exists\, S \text{ for } G^{\mathrm{dbl}}:\ S \text{ is PCC} \ \wedge\ \mathrm{val}(S) = 1\bigr) \;\Longrightarrow\; \bigl(\exists\, S' \text{ for } (G^{k})^{\mathrm{dbl}}:\ S' \text{ is PCC} \ \wedge\ \mathrm{val}(S') = 1\bigr).$$
--
--   This is the completeness half of the parallel repetition of normal form verifiers at the level of games, in the doubled reading that `Verifier.HasPerfectPCC` uses, and it is the statement consumed downstream.
--
--   **Formalization Note** `Game.doubled G : SynchronousGame (Bool × X) A` has `μ p q := if p.1 = false ∧ q.1 = true then G.μ p.2 q.2 else 0` and `D p q a b := if p.1 = false ∧ q.1 = true then G.D p.2 q.2 a b else false`; it is synchronous for any `G`. `SyncStrategy.value` is the tracial value against the normalized trace `Tr/d` on `Matrix (Fin d) (Fin d) ℂ` (`SyncStrategy.value_eq` is the sum above, with the real part of the trace), and `SyncStrategy.IsPCC` quantifies over the question pairs of positive weight. The statement is `∀ k, (∃ S : SyncStrategy G.doubled, S.IsPCC ∧ S.value = 1) → ∃ S' : SyncStrategy (G.repeat k).doubled, S'.IsPCC ∧ S'.value = 1`, with `G : Game X X A A` implicit, `k : ℕ` explicit (`k = 0` included) and `[Fintype X] [Fintype A] [DecidableEq A]`. Blueprint `lem:tensor-power-pcc`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/TensorPower.lean#L301-L308; blueprint lem:tensor-power-pcc

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower

open MIPRE
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]

theorem MIPRE.exists_perfectPCC_repeat_doubled {G : Game X X A A} (k : ℕ)
    (h : ∃ S : SyncStrategy G.doubled, S.IsPCC ∧ S.value = 1) :
    ∃ S' : SyncStrategy (G.repeat k).doubled, S'.IsPCC ∧ S'.value = 1 := by sorry
