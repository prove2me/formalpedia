-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_display_7_3
-- name    : GraphonMF.SparseRate.display_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:53.971747+00:00
-- url     : https://prove2.me/theorems/86ce0125-d2c6-4dbb-8580-44a80becc7e3
-- title:
--   §7.3, pp. 3616–3617 — under Condition 2.3 the discretization term R^{n,4}_s (with G in place of G_n) is at most κ/n²
-- statement:
--   Let Conditions 4.1(a)–(c) and 2.3 hold for the initial laws, the coefficients and a graphon $G$, and let $X$ solve the limit system (4.2), with $\mu_{v,s}=\mathcal L(X_v(s))$. For $n\ge1$ and $s\in[0,T]$ let
--   $$R^{n,4}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G\big(\tfrac in,\tfrac jn\big)\,\mu_{j/n,s}(dx)-\int_I\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G\big(\tfrac in,v\big)\,\mu_{v,s}(dx)\,dv\Big|^2 .$$
--   Then there is a constant $\kappa$ such that
--   $$R^{n,4}_s\le\frac{\kappa}{n^2}\qquad\text{for all }n\in\mathbb N\text{ and }s\in[0,T].$$
--
--   This is the discretization error of replacing the graphon average over $v\in I$ by the average over the grid $j/n$; with (7.15) and Gronwall's inequality it gives the rate of Theorem 4.2. Its proof uses Condition 2.3, Theorem 2.1(b) and Remark 2.4.
--
--   **Formalization Note** The page says "it suffices to argue $R^{n,4}_s\le\kappa/n$" and its display then concludes $\le\kappa/n^2$; the displayed (stronger) bound is stated. $R^{n,4}_s$ is the fourth term of (7.2) with $G_n(i/n,j/n)$ replaced by $G(i/n,j/n)$, as the page writes it under Condition 4.3. At $n=0$ both sides are $0$ by the conventions of Lean ($1/0=\infty$ times an empty sum, $\kappa/0=0$). No edge variables and no $n$-particle system enter.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3616–3617, §7.3, display after 'using Condition 4.3 we have'

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- §7.3 (pp. 3616–3617): the discretization term of (7.2) with `G` in place of `G_n` satisfies
`R^{n,4}_s ≤ κ/n²` for all `n` and `s ≤ T`, under Conditions 4.1(a)–(c) and 2.3. -/
theorem display_7_3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (h41a : Cond41a μ0) (h41b : Cond41b b) (h41c : Cond41c σ)
    {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G) {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∃ κ : ℝ, ∀ (n : ℕ) (s : ℝ≥0), s ≤ T →
      Rn4 P b G X n s ≤ ENNReal.ofReal (κ / (n : ℝ) ^ 2) := by sorry

end GraphonMF.SparseRate
