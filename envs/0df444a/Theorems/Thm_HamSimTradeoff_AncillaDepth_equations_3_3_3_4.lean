-- Prove2me | Theorems.Thm_HamSimTradeoff_AncillaDepth_equations_3_3_3_4
-- name    : HamSimTradeoff.AncillaDepth.equations_3_3_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:47:01.393322+00:00
-- url     : https://prove2.me/theorems/e0b76b04-9458-4b43-ad9a-9b3c100f2d10
-- title:
--   Eqs. (3.3)–(3.4) — full Taylor expansion and nonvanishing
-- statement:
--   For every integer $k\ge1$, the explicitly recursive coefficients $c_{k,n}$ satisfy $c_{k,0}=1/2$ and $c_{k,n}=0$ for $1\le n<k$. For every real $h$, the convergent expansion is
--   $$\rho_k(h)=\frac12+\sum_{n=k}^{\infty}c_{k,n}h^{2n}.$$
--   For $k\ge2$ and every $n\ge0$,
--   $$c_{k,n}=c_{k-1,n}\bigl[4u_k^{2n+1}+(1-4u_k)^{2n+1}\bigr],\qquad c_{1,n}=\frac{(-1)^n}{2^{2n+1}(2n+1)!}.$$
--   Finally $c_{k,n}\ne0$ for every $n\ge k$. These conclusions retain both the missing lower powers and the entire infinite expansion, needed to identify all response derivatives.
--
--   Differences from the source:
--   - encoding: infinite series beginning at n=k → HasSum of the sequence indexed by n=j+k for j≥0; reason: HasSum records convergence as well as the value and avoids default values for divergent sums
--   - encoding: ρ₁(h)=sin(h/2)/h and its Taylor series → ρ₁(0)=1/2 and ρ₁(h)=sin(h/2)/h for h≠0; reason: the Taylor series specifies the removable singularity; ordinary Lean division gives 0 at 0/0
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.15–16, §3.1, Eqs. (3.3)–(3.4) and following nonvanishing sentence

import Definitions.Def_HamSimTradeoff_AncillaDepth_Response
import Definitions.Def_HamSimTradeoff_AncillaDepth_ExponentialSums
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth

/-- Full convergent expansion, missing powers, recurrence and nonvanishing, pp.15–16. -/
theorem equations_3_3_3_4 (k : ℕ) (hk : 1 ≤ k) :
    coefficient k 0 = 1 / 2 ∧
    (∀ n : ℕ, 1 ≤ n → n < k → coefficient k n = 0) ∧
    (∀ h : ℝ, HasSum (fun j : ℕ => coefficient k (j + k) * h ^ (2 * (j + k)))
      (rho k h - 1 / 2)) ∧
    (∀ n : ℕ, k ≤ n → coefficient k n ≠ 0) ∧
    (2 ≤ k → ∀ n : ℕ, coefficient k n = coefficient (k - 1) n *
      (4 * u k ^ (2 * n + 1) + (1 - 4 * u k) ^ (2 * n + 1))) ∧
    (∀ n : ℕ, coefficient 1 n =
      (-1 : ℝ) ^ n / (2 ^ (2 * n + 1) * (Nat.factorial (2 * n + 1) : ℝ))) := by sorry

end HamSimTradeoff.AncillaDepth
