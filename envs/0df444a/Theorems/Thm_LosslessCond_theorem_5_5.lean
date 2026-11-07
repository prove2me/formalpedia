-- Prove2me | Theorems.Thm_LosslessCond_theorem_5_5
-- name    : LosslessCond.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:34:01.505782+00:00
-- url     : https://prove2.me/theorems/b4992f25-4874-4322-a056-a75a70934d07
-- title:
--   Theorem 5.5 — nearly maximal condensation with $k\ge\max\{(\varepsilon c-4)/3,(\varepsilon c-\ell-3)/2\}$
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $D(M)=c\ge 4$, let $0<\varepsilon<1$ be real, and put $\ell=\lceil\log(c+1)\rceil$. There are an integer $1\le k\le c-1$ and an original $2^k\times 2^k$ submatrix $N$, on exactly $2^k$ distinct original rows and $2^k$ distinct original columns, such that
--   $$
--   D(N)\ge(1-\varepsilon)(k+1)\qquad\text{and}\qquad k\ge\max\Bigl\{\frac{\varepsilon c-4}{3},\ \frac{\varepsilon c-\ell-3}{2}\Bigr\}.
--   $$
--
--   This is the quantitative form of Theorem 1.1: high rank supplies a maximally hard nonsingular minor, low rank a larger square losing few bits.
--
--   Differences from the source:
--   - encoding: real inequalities with ⌈log(c + 1)⌉ → compared in ℝ with casts; ℓ = Nat.clog 2 (c + 1); c − 1 in ℕ; reason: same inequalities; c − 1 is exact since c ≥ 4
--   - encoding: D(M[U, V]) for the submatrix on U × V → DetCCHard.commCost M U V, the least depth of a protocol on all of X, Y correct on U × V; reason: protocols restrict and extend, so the two costs agree on every instance
--   - encoding: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite set is equivalent to a type in universe 0; where nonemptiness matters it is assumed or forced by the other hypotheses
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Theorem 5.5, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_DetCCHard_commCost

namespace LosslessCond

/-- **Theorem 5.5 (Nearly maximal condensation)** (Mackenzie, *Lossless Hardness Condensation in
Deterministic Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.16).
Let `D(M) = c ≥ 4`, let `0 < ε < 1`, and put `ℓ = ⌈log(c + 1)⌉`. There are an integer
`1 ≤ k ≤ c − 1` and an original `2^k`-by-`2^k` submatrix `N` such that
`D(N) ≥ (1 − ε)(k + 1)` and `k ≥ max{(εc − 4)/3, (εc − ℓ − 3)/2}`.

**Formalization Note** `N = M[U, V]` for `Finset`s `U`, `V` of original labels with exactly `2^k`
elements each, and `D(N) = DetCCHard.commCost M U V`. `ε` is real; the inequalities are compared in
`ℝ`. `c − 1` is natural subtraction, exact since `c ≥ 4`. -/
theorem theorem_5_5 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (c : ℕ)
    (hc : DetCCHard.Dcost M = c) (hc4 : 4 ≤ c) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ c - 1 ∧ ∃ (U : Finset X) (V : Finset Y),
      U.card = 2 ^ k ∧ V.card = 2 ^ k ∧
      (1 - ε) * ((k : ℝ) + 1) ≤ (DetCCHard.commCost M (U : Set X) (V : Set Y) : ℝ) ∧
      max ((ε * c - 4) / 3) ((ε * c - Nat.clog 2 (c + 1) - 3) / 2) ≤ (k : ℝ) := by sorry

end LosslessCond
