-- Prove2me | Theorems.Thm_Helfgott_etaPlus_prime_projection_error_le
-- name    : Helfgott.etaPlus_prime_projection_error_le
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T09:28:10.350732+00:00
-- url     : https://prove2.me/theorems/99333977-b7fe-49e0-971f-905f6b4ac38c
-- title:
--   Explicit full square-energy error for the Goldbach prime-support projection
-- statement:
--   For $x\ge1$, use the published actual smoothing $\eta_+$, put $c_n=\Lambda(n)\eta_+(n/x)$, and retain $p_n=c_n$ only when $n$ is prime and $n>\sqrt{x}$. The complete discarded square energy obeys
--
--   $$\sum_{n\ge0}|c_n-p_n|^2\le 140000\,x^{9/16}.$$
--
--   Every small-prime coefficient and every proper prime-power coefficient is included. The proof is unconditional and retains the full infinite smoothing tail. It supplies an explicit, sublinear-in-x error for the full-coefficient prime large sieve in the actual minor-arc argument. The constant is deliberately coarse and does not by itself recover the final numerical minor-arc constant in Helfgott (7.48).
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, prime-support projection in Theorem 6.3 and section 7.3. Complete original elementary square-energy estimate, using Mathlib prime-power factorization, geometric series, integral comparisons, Gaussian bounds, and the checked actual smoothing analysis. The earlier proper-prime-power injection attribution to jjosh and all library attributions are retained. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem etaPlus_prime_projection_error_le (x : ℝ) (hx : 1 ≤ x) :
    (∑' n : ℕ, ‖((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) -
      (if Nat.Prime n ∧ Real.sqrt x < (n : ℝ) then
        ((vonMangoldt n*etaPlus ((n : ℝ)/x) : ℝ) : ℂ) else 0)‖^2) ≤
      140000*x^(9/16 : ℝ) := by sorry

end Helfgott
