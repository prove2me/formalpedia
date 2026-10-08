-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_delta_geometric_decay
-- name    : KhachiyanRound.BCD.delta_geometric_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:35.694983+00:00
-- url     : https://prove2.me/theorems/8b548596-ecd5-4b4d-8d55-73e5fa35848b
-- title:
--   (2.25), p. 313 — while εⱼ ≥ 1, δ_k ≤ δ₀(1 − c₁/n)^k ≤ δ₀e^{−c₁k/n}, c₁ = 1 − 1/(2 ln 2)
-- statement:
--   Under the assumptions of Lemma 3, let $\delta_k = F^* - F(p_k)$ and $c_1 = 1 - \frac{1}{2\ln 2} > 0$. For every $k$ such that $\varepsilon_j \ge 1$ for all $j < k$,
--   $$\delta_k \le \delta_0\Big(1 - \frac{c_1}{n}\Big)^k \le \delta_0\, e^{-c_1 k/n}.$$
--
--   While the accuracy is at least $1$, the optimality gap decays geometrically; this gives the first phase $K(1) = O(n(\ln n + \ln\ln m))$ of the iteration bound.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 313, (2.25), proof of Lemma 4

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem delta_geometric_decay {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → Fin n → ℝ)
    (hsymm : IsCentrallySymmetric a) (hfull : affineSpan ℝ (Set.range a) = ⊤) (hn : 2 ≤ n)
    (p : ℕ → ι → ℝ) (hrun : IsBCDRun a p) :
    ∀ k : ℕ, (∀ j < k, 1 ≤ epsOf a (p j)) →
      Fstar a - F a (p k) ≤
          (Fstar a - F a (p 0)) * (1 - (1 - 1 / (2 * Real.log 2)) / (n : ℝ)) ^ k ∧
        (Fstar a - F a (p 0)) * (1 - (1 - 1 / (2 * Real.log 2)) / (n : ℝ)) ^ k ≤
          (Fstar a - F a (p 0)) * Real.exp (-((1 - 1 / (2 * Real.log 2)) * k / (n : ℝ))) := by sorry
end KhachiyanRound.BCD
