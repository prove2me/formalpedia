-- Prove2me | Theorems.Thm_LiuVanRyzin_optimal_stocking
-- name    : LiuVanRyzin.optimal_stocking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:39:26.190136+00:00
-- url     : https://prove2.me/theorems/5a2bf6f9-c5d0-4a1f-a6aa-4463bfeb5ccc
-- title:
--   Proposition 3 — rationing is optimal if $\bar U\ge U_c$; otherwise serve the whole market at the low price
-- statement:
--   A monopolist sells to $N>0$ customers whose valuations are uniform on $[0,\bar U]$, at prices $p_1$ in period 1 and $p_2$ in period 2 with $\alpha<p_2<p_1$, where $\alpha$ is the unit cost. Customers have power utility $u(x)=x^\gamma$, $0<\gamma<1$. Let $v^0>p_1$ be the solution of the first-order condition (7),
--   $$\left(\frac{v^0-p_1}{v^0-p_2}\right)^\gamma\left(1+\frac{\gamma(p_1-p_2)}{v^0-p_1}\right)=\frac{p_1-\alpha}{p_2-\alpha},$$
--   and let
--   $$U_c=\frac{(p_2+\gamma(p_1-\alpha))v^0-p_2(p_1+\gamma(p_2-\alpha))}{v^0-p_1+\gamma(p_1-p_2)}.$$
--   Let $\Pi(v)$ be the segmented-market profit (6) and $\Pi^{NS}=(p_2-\alpha)\frac{N}{\bar U}(\bar U-p_2)$ the profit of serving the entire market at the low price. Then:
--
--   1. If $\bar U\ge U_c$, inducing segmentation by rationing is optimal: $v^0\in[p_1,\bar U]$, $v^0$ maximizes $\Pi$ over $[p_1,\bar U]$, and $\Pi(v^0)\ge\Pi^{NS}$. The optimal solution is $v^*=v^0$, fill rate $q^*=q^0=((v^0-p_1)/(v^0-p_2))^\gamma$ and stocking quantity $C^*=C^0=\frac N{\bar U}(\bar U-v^0+(v^0-p_2)q^0)$.
--   2. If $\bar U<U_c$, serving the entire market at the low price is optimal: $\Pi(v)\le\Pi^{NS}$ for every $v\in[p_1,\bar U]$. The optimal solution is $v^*=\bar U$, $q^*=1$, $C^*=\frac N{\bar U}(\bar U-p_2)$.
--
--   Here "optimal" is the paper's: the firm's optimal profit is the larger of the segmented optimum $\Pi^0=\max_{p_1\le v\le\bar U}\Pi(v)$ and $\Pi^{NS}$. The theorem says rationing pays exactly when there are enough high-value customers.
--
--   **Formalization Note** The paper uses $0\le p_2<\bar U$ without stating it: the uniform law gives $N\bar F(p_2)=\frac N{\bar U}(\bar U-p_2)$ only for $p_2\in[0,\bar U]$, and it makes $\bar U>0$. The optimal $q^0$ and $C^0$ are `fillRate` and `capacity` at $v^0$ (definition module), so they are not restated as conjuncts.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1122, Proposition 3 (with Eqs. (6)–(8); optimality as max(Π⁰, Π^NS), p. 1121)

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- Proposition 3 (Liu–van Ryzin 2008, p. 1122). Let `v⁰` be the root of (7) and `U_c` as in
(8). If `Ū ≥ U_c`, segmentation at `v⁰` is optimal: `v⁰` maximizes `Π` on `[p₁, Ū]` and
`Π(v⁰) ≥ Π^NS`. Otherwise serving the entire market at the low price is optimal:
`Π(v) ≤ Π^NS` for every `v ∈ [p₁, Ū]`. -/
theorem optimal_stocking (N Ubar p₁ p₂ α γ v₀ : ℝ) (hN : 0 < N) (hα : α < p₂)
    (hp : p₂ < p₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp₂ : 0 ≤ p₂) (hpU : p₂ < Ubar)
    (hv₀ : p₁ < v₀) (hroot : focLHS p₁ p₂ α γ v₀ = 0) :
    (criticalU p₁ p₂ α γ v₀ ≤ Ubar →
        v₀ ∈ Set.Icc p₁ Ubar ∧
          IsMaxOn (segProfit N Ubar p₁ p₂ α γ) (Set.Icc p₁ Ubar) v₀ ∧
          lowPriceProfit N Ubar p₂ α ≤ segProfit N Ubar p₁ p₂ α γ v₀) ∧
      (Ubar < criticalU p₁ p₂ α γ v₀ →
        ∀ v ∈ Set.Icc p₁ Ubar, segProfit N Ubar p₁ p₂ α γ v ≤ lowPriceProfit N Ubar p₂ α) := by sorry

end LiuVanRyzin
