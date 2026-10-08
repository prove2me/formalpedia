-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_rank_one_correction
-- name    : KhachiyanRound.BCD.rank_one_correction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:51.917984+00:00
-- url     : https://prove2.me/theorems/236210a8-ae4a-46d2-a662-e9a8016c73ac
-- title:
--   p. 314 — the rank-one correction A_{k+1}⁻¹ = (1 + ε/((n−1)(1+ε)))A_k⁻¹ − (ε/((n−1)(1+ε)²)) b bᵗ
-- statement:
--   Let $n \ge 2$, $a_1,\dots,a_m \in \mathbb{R}^n$ and $p \in S_F$. Let $r$ be an index maximizing $w_j(p)$, let $\varepsilon = \varepsilon(p)$, $\tau = \varepsilon/(w_r(p) - 1)$, and let $p' = (1-\tau)p + \tau e_r$ be the BCD step from $p$. With $A = A(p)$ and $b = A^{-1}a_r$,
--   $$A(p')^{-1} = \Big(1 + \frac{\varepsilon}{(n-1)(1+\varepsilon)}\Big)A^{-1} - \frac{\varepsilon}{(n-1)(1+\varepsilon)^2}\, b\, b^{\mathsf T}.$$
--
--   The inverse moment matrix is thus updated by a rank-one correction, which is what makes each BCD iteration cost $O(nm)$ arithmetic operations.
--
--   **Formalization Note** Only the matrix identity is formalized; the operation count $O(nm)$ per iteration is not. Central symmetry (2.1) and full dimension (2.2) are not needed ($p \in S_F$ already makes $A$ invertible) and are dropped; $n \ge 2$ is kept, as the formula divides by $n-1$.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 314, rank-one corrections after the proof of Lemma 4

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem rank_one_correction {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ) (hn : 2 ≤ n) (p : ι → ℝ) (hp : p ∈ SF a)
    (r : ι) (hr : ∀ j, w a p j ≤ w a p r)
    (ε τ : ℝ) (hε : ε = epsOf a p) (hτ : τ = ε / (w a p r - 1))
    (b : Fin n → ℝ) (hb : b = (momentMatrix a p)⁻¹.mulVec (a r)) :
    (momentMatrix a ((1 - τ) • p + τ • Pi.single r 1))⁻¹ =
      (1 + ε / (((n : ℝ) - 1) * (1 + ε))) • (momentMatrix a p)⁻¹ -
        (ε / (((n : ℝ) - 1) * (1 + ε) ^ 2)) • Matrix.vecMulVec b b := by sorry
end KhachiyanRound.BCD
