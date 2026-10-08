-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_fp_scarce_exact
-- name    : GVRPricing.FixedPrice.fp_scarce_exact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:00:26.755914+00:00
-- url     : https://prove2.me/theorems/dd45b856-86e3-4949-bebc-aa1c222049b9
-- title:
--   Remark after Theorem 3 — for λ*t > n, J^FP(n,t) = np⁰(1 − (nⁿ/n!)e^{−n})
-- statement:
--   Let $(\Lambda,p,\lambda^*)$ be a regular demand function, $n\ge1$ a stock and $t>0$ a horizon with $\lambda^*t>n$. The fixed-price heuristic, which prices at the run-out price $p^0=p(n/t)$, earns exactly
--   $$J^{FP}(n,t)=np^0\Big(1-\frac{n^n}{n!}e^{-n}\Big).$$
--
--   This gives a slightly better guarantee than Theorem 3 for small $n$ with the same rate of convergence, since $(n^n/n!)e^{-n}\sim1/\sqrt{2\pi n}$ by Stirling's formula.
--
--   **Formalization Note** The page justifies the formula by "$E(N_n-n)^+=n(1-P\{N_n=n\})$" for $N_n$ Poisson with mean $n$. That identity is a slip: $E(N_n-n)^+=nP\{N_n=n\}$, and it is $E[\min\{N_n,n\}]$ that equals $n(1-P\{N_n=n\})$ (for $n=1$: $E(N_1-1)^+=e^{-1}\approx0.368$, while $1-P\{N_1=1\}\approx0.632$). The displayed formula for $J^{FP}$ is correct and is what is stated.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1008 (PDF 10), §3.3, Remark after Theorem 3

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_SalesProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GVRPricing.FixedPrice

/-- **Remark after Theorem 3** (p. 1008). If `λ* t > n ≥ 1` (`t > 0`), the fixed-price revenue is
exactly `J^FP(n, t) = n p⁰ (1 − (nⁿ/n!) e^{−n})` with `p⁰ = p(n/t)`. (The page's intermediate
claim `E(N_n − n)⁺ = n(1 − P{N_n = n})` is a slip: it is `E[min{N_n, n}]` that equals
`n(1 − P{N_n = n})`; the displayed formula for `J^FP` is correct.) -/
theorem fp_scarce_exact (M : Model) (n : ℕ) (t : ℝ) (hn : 1 ≤ n) (ht : 0 < t)
    (h : (n : ℝ) < M.lstar * t) :
    fpValue M n t =
      ENNReal.ofReal (n * M.p (n / t) * (1 - (n : ℝ) ^ n / (Nat.factorial n) * Real.exp (-n))) := by sorry

end GVRPricing.FixedPrice
