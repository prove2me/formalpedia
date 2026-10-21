-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_theorem_1_part_3_steps_1_2
-- name    : NetworkVolatility.Robust.theorem_1_part_3_steps_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:04.159971+00:00
-- url     : https://prove2.me/theorems/7fe5d62a-bb92-4aae-86fb-78d78ffb1cd3
-- title:
--   Proof of Theorem 1, Part 3, Steps 1–2, p. 13 — normalization $f^\top L^{-1}f=1$ and $f^\top L^{-1}f-f^\top(I-\alpha\tilde W)^{-1}f=f^\top L^{-1}Mf$
-- statement:
--   Let $W$ and $\tilde W$ be real symmetric $n\times n$ matrices and $\alpha\in\mathbb R$ such that $L=I-\alpha W$ and $I-\alpha\tilde W$ are invertible, and set
--   $$M=I-(I-\alpha W)(I-\alpha\tilde W)^{-1}.$$
--   For every $f\in\mathbb R^n$:
--
--   1. (Step 1) if $q=f^\top L^{-1}f>0$, then $f'=q^{-1/2}f$ satisfies $f'^\top L^{-1}f'=1$ and
--   $$\left|\frac{f'^\top L^{-1}f'-f'^\top(I-\alpha\tilde W)^{-1}f'}{f'^\top L^{-1}f'}\right|=\left|\frac{f^\top L^{-1}f-f^\top(I-\alpha\tilde W)^{-1}f}{f^\top L^{-1}f}\right|;$$
--   2. (Step 2) $f^\top L^{-1}f-f^\top(I-\alpha\tilde W)^{-1}f=f^\top L^{-1}Mf$, and both $L^{-1}M$ and $L^{-1}$ are symmetric.
--
--   Together these reduce the upper bound of Theorem 1 to bounding the quadratic form $f^\top L^{-1}Mf$ on the ellipsoid $f^\top L^{-1}f=1$.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 13, proof of Theorem 1, Part 3, Steps 1–2

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Matrix

/-- Proof of Theorem 1, Part 3, Steps 1–2, p. 13. Let `W`, `W̃` be symmetric with `L = I - αW` and
`I - αW̃` invertible, and `M = I - L(I - αW̃)⁻¹`.
Step 1: if `q = fᵀL⁻¹f > 0`, then `f' = q^{-1/2} f` satisfies `f'ᵀL⁻¹f' = 1` and has the same
relative change `|(f'ᵀL⁻¹f' - f'ᵀ(I - αW̃)⁻¹f') / f'ᵀL⁻¹f'|` as `f`.
Step 2: `fᵀL⁻¹f - fᵀ(I - αW̃)⁻¹f = fᵀL⁻¹Mf` for every `f`, and `L⁻¹M` and `L⁻¹` are symmetric. -/
theorem theorem_1_part_3_steps_1_2 {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hW : W.IsSymm) (hWt : Wt.IsSymm) (hL : IsUnit (1 - α • W)) (hLt : IsUnit (1 - α • Wt))
    (f : Fin n → ℝ) :
    (0 < f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f) →
      let f' := (Real.sqrt (f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f)))⁻¹ • f
      f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f') = 1 ∧
      |(f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f') - f' ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f')) /
          f' ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f')| =
        |(f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f) - f ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f)) /
          f ⬝ᵥ ((1 - α • W)⁻¹ *ᵥ f)|) ∧
    (let L := 1 - α • W
     let M := 1 - L * (1 - α • Wt)⁻¹
     f ⬝ᵥ (L⁻¹ *ᵥ f) - f ⬝ᵥ ((1 - α • Wt)⁻¹ *ᵥ f) = f ⬝ᵥ ((L⁻¹ * M) *ᵥ f) ∧
       (L⁻¹ * M).IsSymm ∧ (L⁻¹).IsSymm) := by sorry

end NetworkVolatility.Robust
