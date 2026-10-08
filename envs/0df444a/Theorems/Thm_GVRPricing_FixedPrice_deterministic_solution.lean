-- Prove2me | Theorems.Thm_GVRPricing_FixedPrice_deterministic_solution
-- name    : GVRPricing.FixedPrice.deterministic_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:03:16.612602+00:00
-- url     : https://prove2.me/theorems/43278370-3a67-48b0-8119-66a58762fbb1
-- title:
--   Proposition 2 — the constant rate λ^D = min{λ*, x/t} solves the deterministic problem (11); J^D(x,t) = t r(λ^D)
-- statement:
--   Let $(\Lambda,p,\lambda^*)$ be a regular demand function, $x\ge0$ a stock and $t>0$ a horizon. Write $\lambda^0=x/t$ for the **run-out rate**, $p^0=p(\lambda^0)$ and $r^0=p^0\lambda^0$, and set
--   $$\lambda^D=\min\{\lambda^*,\lambda^0\}.$$
--   Then:
--
--   1. the constant path $\lambda(s)=\lambda^D$, $0\le s\le t$, is feasible for the deterministic problem (11);
--   2. it is optimal: every feasible rate path $\lambda(\cdot)$ satisfies $\int_0^t r(\lambda(s))\,ds\le t\,r(\lambda^D)$;
--   3. the optimal revenue is
--   $$J^D(x,t)=t\,r(\lambda^D),$$
--   which equals $t\min\{r^*,r^0\}$ when $x\le\lambda^*t$, and $t\,r^*$ when $x\ge\lambda^*t$;
--   4. in terms of price, $p^D=p(\lambda^D)=\max\{p^*,p^0\}$ (when $\lambda^*>0$, $x>0$ and $\lambda^0\in\Lambda$, so that both prices are finite).
--
--   If items are plentiful ($x\ge\lambda^*t$) the firm prices at the revenue-maximizing level; if they are scarce it prices to sell exactly its stock. This solution supplies the fixed-price heuristic and the value against which Theorems 2 and 3 compare the stochastic problem.
--
--   **Formalization Note** The page prints $J^D(x,t)=t\min\{r^*,r^0\}$ (eq. (12)) without a case distinction. That is wrong when $x>\lambda^*t$: there $r^0=r(\lambda^0)\le r^*$, so $t\min\{r^*,r^0\}=t\,r^0$, while the optimum is $t\,r^*$. For exponential demand $ae^{-p}$ with $x=at$, $r^0=0$ but $J^D=a t/e$. The statement gives the corrected value $t\,r(\lambda^D)$, and the printed form in the case $x\le\lambda^*t$, where it is right. The page calls $\lambda^D$ "the" optimal solution; under concavity alone it need not be unique, so the statement asserts optimality, not uniqueness. When $\lambda^0\notin\Lambda$ the run-out quantities $p^0$, $r^0$ are undefined, and the statement uses them only where $\lambda^0\in\Lambda$. The OCR's "$p(\lambda_0)$" is a typesetting slip for $p(\lambda^0)$.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1006 (PDF 8), §3.2, Proposition 2, eq. (12)

import Mathlib
import Definitions.Def_GVRPricing_FixedPrice_Model
import Definitions.Def_GVRPricing_FixedPrice_Deterministic

open MeasureTheory Set

namespace GVRPricing.FixedPrice

/-- **Proposition 2** (p. 1006), with the value (12) corrected. For a stock `x ≥ 0` and a
horizon `t > 0`, with run-out rate `λ⁰ = x/t` and `λ^D = min{λ*, λ⁰}`:
1. the constant path `λ(s) = λ^D` is feasible for (11);
2. it is optimal: every feasible rate path earns at most `∫_0^t r(λ^D) ds`;
3. the optimal revenue is `J^D(x, t) = t r(λ^D)`, which equals `t min{r*, r⁰}` (`r⁰ = r(λ⁰)`)
   when `x ≤ λ* t` and `t r*` when `x ≥ λ* t` (the printed `t min{r*, r⁰}` is wrong for
   `x > λ* t`, where `r⁰ ≤ r*`);
4. in terms of price, `p^D = p(λ^D) = max{p*, p⁰}` whenever both prices are finite
   (`λ* > 0`, `x > 0`, `λ⁰ ∈ Λ`). -/
theorem deterministic_solution (M : Model) (x t : ℝ) (hx : 0 ≤ x) (ht : 0 < t) :
    IsFeasiblePath M x t (fun _ => min M.lstar (x / t)) ∧
    (∀ ℓ : ℝ → ℝ, IsFeasiblePath M x t ℓ →
      ∫ s in (0 : ℝ)..t, M.r (ℓ s) ≤ ∫ s in (0 : ℝ)..t, M.r (min M.lstar (x / t))) ∧
    detValue M x t = t * M.r (min M.lstar (x / t)) ∧
    (x ≤ M.lstar * t → detValue M x t = t * min M.rstar (M.r (x / t))) ∧
    (M.lstar * t ≤ x → detValue M x t = t * M.rstar) ∧
    (0 < M.lstar → 0 < x → x / t ∈ M.Λ →
      M.p (min M.lstar (x / t)) = max M.pstar (M.p (x / t))) := by sorry

end GVRPricing.FixedPrice
