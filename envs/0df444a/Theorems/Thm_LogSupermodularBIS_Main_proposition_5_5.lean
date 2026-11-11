-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_proposition_5_5
-- name    : LogSupermodularBIS.Main.proposition_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:31.162995+00:00
-- url     : https://prove2.me/theorems/ee556e12-1441-4561-b293-2e060297104d
-- title:
--   Proposition 5.5 — the smoothed guide is near-optimal
-- statement:
--   Let $\Phi$ be a supermodular potential on $\{0,1\}^d$ with $\Phi(0)=0$, $\mu=e^\Phi/Z_\Phi$, and $0<w\le1/2$. The guide $g$ of (5.2) has the following properties.
--   1. $g$ is a guide.
--   2. With $X\sim\mu$, $c_i=1-p_i(X_{<i})$ and $\Delta_w(c)=H(c)-\tfrac12H(c-h(c))-\tfrac12H(c+h(c))$,
--   $$H(\mu)-\sum_{i=1}^dE[a(U_i)g_i(U)]=\sum_{i=1}^dE\Delta_w(c_i).\tag{5.3}$$
--   3. For every $c\in[0,1]$, $0\le\Delta_w(c)\le w^2c(1-c)$.
--   4. $E\Phi^L(g(U))\ge E_\mu\Phi$. Consequently
--   $$0\le\log Z_\Phi-\mathcal P(g)\le w^2\sum_{i=1}^dE[c_i(1-c_i)]\le\frac{dw^2}4.\tag{5.4}$$
--
--   Differences from the source:
--   - encoding: coordinates and rows 1, …, d → Fin d, indices 0, …, d−1; reason: index shift only
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 27 (PDF 28), Proposition 5.5, (5.3), (5.4)

import Definitions.Def_LogSupermodularBIS_Main_Smoothing

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Proposition 5.5 (Near-optimal objective value for the smoothed guide), p. 27. Here
`c_i(x) = 1 − p_i(x_{<i})` and expectations over `X ∼ μ` are sums against `μ = e^Φ / Z_Φ`. -/
theorem proposition_5_5 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0)
    (hsup : Supermodular Φ) (w : ℝ) (hw : w ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    let g := smoothedGuide Φ w
    let μ := potentialLaw Φ
    let c : (Fin d → Bool) → Fin d → ℝ := fun x i => 1 - condMarginal Φ (prefixOf x i.val)
    IsGuide d g ∧
    lawEntropy μ - linearScore g = ∑ i : Fin d, ∑ x, μ x * smoothingLoss w (c x i) ∧
    (∀ c ∈ Set.Icc (0 : ℝ) 1, 0 ≤ smoothingLoss w c ∧ smoothingLoss w c ≤ w ^ 2 * c * (1 - c)) ∧
    ∑ x, μ x * Φ x ≤ ∫ u, lovaszExt Φ (g u) ∂unifCube d ∧
    0 ≤ Real.log (potentialPartition Φ) - variationalObjective Φ g ∧
    Real.log (potentialPartition Φ) - variationalObjective Φ g ≤
      w ^ 2 * ∑ i : Fin d, ∑ x, μ x * (c x i * (1 - c x i)) ∧
    w ^ 2 * ∑ i : Fin d, ∑ x, μ x * (c x i * (1 - c x i)) ≤ d * w ^ 2 / 4 := by sorry

end LogSupermodularBIS.Main
