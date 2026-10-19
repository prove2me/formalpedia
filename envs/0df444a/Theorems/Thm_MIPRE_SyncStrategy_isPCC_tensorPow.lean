-- Prove2me | Theorems.Thm_MIPRE_SyncStrategy_isPCC_tensorPow
-- name    : MIPRE.SyncStrategy.isPCC_tensorPow
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:43:57.994066+00:00
-- url     : https://prove2.me/theorems/dcba1321-1318-40a0-85bf-281752024cd5
-- title:
--   The tensor power of a PCC synchronous strategy is PCC
-- statement:
--   Let $H$ be a synchronous game with finite question alphabet $X$ and finite answer alphabet $A$: a probability distribution $\mu$ on $X \times X$ and a decision predicate $D$ on $X \times X \times A \times A$ that rejects unequal answers to equal questions. A synchronous strategy $S = (d, M)$ for $H$ is a dimension $d > 0$ together with, for every question $x$, a projective measurement $\{M^x_a\}_{a \in A}$ on $\mathbb{C}^d$ (self-adjoint idempotent matrices summing to the identity). $S$ is PCC (projective, consistent and commuting) when the measurement operators of any two questions asked with positive probability commute: $M^x_a M^y_b = M^y_b M^x_a$ for all $a, b \in A$ whenever $\mu(x,y) > 0$. For $k \in \mathbb{N}$, the $k$-fold direct repetition $H^{k}$ is the synchronous game on $X^k$, $A^k$ with the product distribution $\mu^{\otimes k}$ and the conjunction of the coordinate predicates, and the tensor power $S^{\otimes k}$ is the strategy for $H^{k}$ of dimension $d^k$ with measurements $M^{\bar x}_{\bar a} = \bigotimes_{i<k} M^{x_i}_{a_i}$.
--
--   If $S$ is PCC, then $S^{\otimes k}$ is PCC for every $k \in \mathbb{N}$:
--
--   $$\forall\, \bar x, \bar y \in X^k,\quad \mu^{\otimes k}(\bar x, \bar y) > 0 \;\Longrightarrow\; \forall\, \bar a, \bar b \in A^k,\quad \Bigl(\textstyle\bigotimes_{i} M^{x_i}_{a_i}\Bigr)\Bigl(\bigotimes_{i} M^{y_i}_{b_i}\Bigr) = \Bigl(\bigotimes_{i} M^{y_i}_{b_i}\Bigr)\Bigl(\bigotimes_{i} M^{x_i}_{a_i}\Bigr).$$
--
--   With `value_tensorPow` (the value of $S^{\otimes k}$ is the $k$-th power of that of $S$), this is the completeness half of the parallel repetition of normal form verifiers at the level of games: perfect PCC strategies survive direct repetition.
--
--   **Formalization Note** `SyncStrategy.IsPCC S` is `∀ x y, 0 < H.μ x y → ∀ a b, S.P.M x a * S.P.M y b = S.P.M y b * S.P.M x a`. `SyncStrategy.tensorPow S k : SyncStrategy (H.repeat k)` has `d := S.d ^ k` and `P := (S.P.tensorPow k).reindexMat (equivFinPow S.d k)`: the operator `tensorFamily (fun i => S.P.M (x i) (a i))` on `ℂ^{Fin k → Fin S.d}`, transported to `Matrix (Fin (S.d ^ k)) (Fin (S.d ^ k)) ℂ` along a noncomputably chosen equivalence `(Fin k → Fin d) ≃ Fin (d ^ k)` (`equivFinPow`). `k = 0` is allowed. The ambient variables are `{X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]` and `{H : SynchronousGame X A}`; `S` is implicit, and `hS : S.IsPCC` and `k : ℕ` are the arguments. Blueprint `lem:tensor-power-pcc`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/TensorPower.lean#L224-L239; blueprint lem:tensor-power-pcc

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
open MIPRE.SyncStrategy
open Matrix
variable {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
variable {H : SynchronousGame X A}

theorem MIPRE.SyncStrategy.isPCC_tensorPow {S : SyncStrategy H} (hS : S.IsPCC) (k : ℕ) : (S.tensorPow k).IsPCC := by sorry
