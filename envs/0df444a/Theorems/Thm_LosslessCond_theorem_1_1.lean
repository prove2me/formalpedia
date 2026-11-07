-- Prove2me | Theorems.Thm_LosslessCond_theorem_1_1
-- name    : LosslessCond.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:38.661017+00:00
-- url     : https://prove2.me/theorems/7be9ced6-d918-4ccb-a2db-d2b15de7f562
-- title:
--   Theorem 1.1 — lossless condensation: a $2^k$-square with $k\ge(\varepsilon c-4)/3$ and $D(N)\ge(1-\varepsilon)(k+1)$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite total Boolean matrix with deterministic communication complexity $D(M)=c\ge 4$. For every real $0<\varepsilon<1$ there are an integer $k$ with $1\le k\le c-1$ and a submatrix $N=M[U,V]$ consisting of exactly $2^k$ distinct original rows $U\subseteq X$ and $2^k$ distinct original columns $V\subseteq Y$ such that
--   $$
--   k\ge\frac{\varepsilon c-4}{3},\qquad D(N)\ge(1-\varepsilon)(k+1).
--   $$
--
--   Since every $2^k\times 2^k$ matrix has a protocol of depth $k+1$, the retained square is nearly maximally hard, at an input length linear in $c$ for fixed $\varepsilon$. This answers the lossless condensation question of Hatami, recorded as Open Problem 2 by Göös, Newman, Riazanov and Sokolov (STOC 2024).
--
--   **Formalization Note** $D$ is the least depth of a deterministic protocol tree with fixed Boolean leaf outputs and free speaking order; $D(N)$ is the least depth of a protocol correct on $U\times V$. "Distinct" refers to labels: row values in $U$ may repeat.
--
--   Differences from the source:
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
--   - encoding: real ε and real inequalities → ε : ℝ, inequalities compared in ℝ with casts; c − 1 in ℕ; reason: same inequalities; c − 1 is exact since c ≥ 4
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_DetCCHard_commCost

namespace LosslessCond

/-- **Theorem 1.1 (Lossless condensation)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.2).
Let `M` be a finite total Boolean matrix with `D(M) = c ≥ 4`. For every `0 < ε < 1`, there are an
integer `1 ≤ k ≤ c − 1` and a submatrix `N` consisting of exactly `2^k` distinct original rows and
`2^k` distinct original columns such that `k ≥ (εc − 4)/3` and `D(N) ≥ (1 − ε)(k + 1)`.

**Formalization Note** A finite total Boolean matrix is a function `M : X → Y → Bool` on finite
types; no `Nonempty` hypothesis is needed since an empty side gives `D(M) = 0 < 4`. `D(M)` is
`DetCCHard.Dcost M`. The submatrix `N = M[U, V]` is given by `Finset`s `U`, `V` of distinct original
labels with exactly `2^k` elements each (row values may repeat), and
`D(N) = DetCCHard.commCost M U V`, the least depth of a protocol correct on `U × V`. `ε` is real
and the inequalities are compared in `ℝ`; `c − 1` is natural subtraction, exact since `c ≥ 4`. -/
theorem theorem_1_1 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (c : ℕ)
    (hc : DetCCHard.Dcost M = c) (hc4 : 4 ≤ c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ c - 1 ∧ ∃ (U : Finset X) (V : Finset Y),
      U.card = 2 ^ k ∧ V.card = 2 ^ k ∧
      (ε * c - 4) / 3 ≤ (k : ℝ) ∧
      (1 - ε) * ((k : ℝ) + 1) ≤ (DetCCHard.commCost M (U : Set X) (V : Set Y) : ℝ) := by sorry

end LosslessCond
