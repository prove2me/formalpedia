-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_weak_angle_right
-- name    : LogBarrierIPM.Curvature.weak_angle_right
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:23:10.559475+00:00
-- url     : https://prove2.me/theorems/9ac9d637-3764-4432-8791-485ab9d0b174
-- title:
--   Proof of Theorem 25 — $\angle^*\mathcal C^{\mathrm{trop}}(\lambda_{k-1})\mathcal C^{\mathrm{trop}}(\lambda_k)\mathcal C^{\mathrm{trop}}(\lambda_{k+1})=\pi/2$ at every interior subdivision point
-- statement:
--   Let $r\ge2$, $\lambda_k=\frac{4k}{2^{r-1}}$ for $k=0,1,\dots,2^{r-2}$, and let $\mathcal C^{\mathrm{trop}}$ be the tropical central path of $\mathbf{LW}_r$, viewed in $\mathbb T^{2N}$. For every $1\le k\le 2^{r-2}-1$,
--   $$\angle^*\,\mathcal C^{\mathrm{trop}}(\lambda_{k-1})\,\mathcal C^{\mathrm{trop}}(\lambda_k)\,\mathcal C^{\mathrm{trop}}(\lambda_{k+1})=\frac\pi2 .$$
--
--   Summed over the $2^{r-2}-1$ interior subdivision points, and combined with Proposition 24, this yields the lower bound $(2^{r-2}-1)\pi/2$ of Theorem 25.
--
--   **Formalization Note** The points are the real vectors of the definition `TropicalCentralPathLW`, cast into `WithBot ℝ`; $\lambda_{k-1}$ is written $4(k-1)/2^{r-1}$ with real subtraction. For $r=2$ the range of $k$ is empty.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 23, proof of Theorem 25, third paragraph

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TropicalAngle
import Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW

namespace LogBarrierIPM.Curvature

/-- Proof of Theorem 25 (p. 23): with `λ_k = 4k/2^{r−1}`,
`∠* C^trop(λ_{k−1}) C^trop(λ_k) C^trop(λ_{k+1}) = π/2` for `1 ≤ k ≤ 2^{r−2} − 1`
(tropical central path of `LW_r`, all `2N` coordinates). -/
theorem weak_angle_right (r k : ℕ) (hr : 2 ≤ r) (hk1 : 1 ≤ k) (hk2 : k + 1 ≤ 2 ^ (r - 2)) :
    let C : ℝ → Fin ((2 * r + (3 * r - 1)) + (2 * r + (3 * r - 1))) → WithBot ℝ :=
      fun lam q => ((tropCentralPathLW r lam q : ℝ) : WithBot ℝ)
    weakTropicalAngle (C (4 * ((k : ℝ) - 1) / 2 ^ (r - 1))) (C (4 * (k : ℝ) / 2 ^ (r - 1)))
      (C (4 * ((k : ℝ) + 1) / 2 ^ (r - 1))) = Real.pi / 2 := by sorry

end LogBarrierIPM.Curvature
