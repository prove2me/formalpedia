-- Prove2me | Theorems.Thm_FracPackCover_Covering_lemma_3_6
-- name    : FracPackCover.Covering.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:09.675902+00:00
-- url     : https://prove2.me/theorems/da98a4bc-052a-4ee6-9629-f3551361c6cb
-- title:
--   Lemma 3.6 — with $m$ oracle calls, an initial $x\in P$ with $Ax\ge\frac1m b$ or a proof that no exact solution exists
-- statement:
--   Let $A\ge0$, $b>0$, $P$ be covering data and let subroutine (7) be an exact maximization oracle. The initial-solution procedure calls the oracle once for each row $i$, with costs $a_i$, obtaining $x_i\in P$ that maximizes $a_ix$ over $P$ ($m$ calls in all), and then:
--   1. if $a_ix_i<b_i$ for some $i$, it reports that there is no exact solution, and indeed no $x'\in P$ has $Ax'\ge b$;
--   2. otherwise it returns $x=\frac1m\sum_i x_i$, which lies in $P$ and satisfies
--   $$Ax\ \ge\ \tfrac1m\, b .$$
--
--   This provides the starting point of the covering algorithm, with $\lambda(x)\ge 1/m$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 20, Lemma 3.6

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_Driver

namespace FracPackCover.Covering

/-- Lemma 3.6 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 20). The initial-solution procedure
`initCover`, which makes `m` calls to subroutine (7) (one with costs `a_i` for each row `i`), either
finds `x ∈ P` with `A x ≥ (1/m) b`, or correctly concludes that there is no exact solution. -/
theorem lemma_3_6 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc) :
    (initCover A b orc = none → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) ∧
    (∀ x, initCover A b orc = some x → x ∈ P ∧ ∀ i, (1 / (m : ℝ)) * b i ≤ rowVal A x i) := by sorry

end FracPackCover.Covering
