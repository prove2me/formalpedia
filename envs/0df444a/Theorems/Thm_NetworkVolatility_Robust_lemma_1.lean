-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_lemma_1
-- name    : NetworkVolatility.Robust.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:09.330263+00:00
-- url     : https://prove2.me/theorems/32da2f6d-c548-4b39-89bb-916f004bad08
-- title:
--   Lemma 1, p. 14 — a maximizer (or minimizer) of $f^\top L^{-1}Mf$ subject to $f^\top L^{-1}f=1$ satisfies $Mf=\mu f$
-- statement:
--   Let $W$ and $\tilde W$ be real symmetric $n\times n$ matrices and $\alpha\in\mathbb R$ such that $L=I-\alpha W$ and $I-\alpha\tilde W$ are invertible, and set $M=I-(I-\alpha W)(I-\alpha\tilde W)^{-1}$. Let $f\in\mathbb R^n$ satisfy $f^\top L^{-1}f=1$.
--
--   1. If $f$ maximizes $g\mapsto g^\top L^{-1}Mg$ over all $g$ with $g^\top L^{-1}g=1$, then $Mf=\mu f$ for some $\mu\in\mathbb R$.
--   2. If $f$ minimizes the same function over the same set, then $Mf=\mu f$ for some $\mu\in\mathbb R$.
--
--   Consequently the extreme values of $|f^\top L^{-1}Mf|$ on the constraint set are absolute values of eigenvalues of $M$ (Step 3 of the proof of Theorem 1).
--
--   **Formalization Note** The lemma is stated as an implication from a maximizer (minimizer); it asserts no existence of one.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 14, Lemma 1 (proof p. 35)

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open Matrix

/-- Lemma 1, p. 14 (proof p. 35). Let `W`, `W̃` be symmetric with `L = I - αW` and `I - αW̃`
invertible, and `M = I - L(I - αW̃)⁻¹`. If `f` maximizes (or minimizes) `gᵀL⁻¹Mg` over all `g` with
`gᵀL⁻¹g = 1`, then `Mf = μf` for some real `μ`. -/
theorem lemma_1 {n : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ) (α : ℝ)
    (hW : W.IsSymm) (hWt : Wt.IsSymm) (hL : IsUnit (1 - α • W)) (hLt : IsUnit (1 - α • Wt))
    (f : Fin n → ℝ) :
    let L := 1 - α • W
    let M := 1 - L * (1 - α • Wt)⁻¹
    f ⬝ᵥ (L⁻¹ *ᵥ f) = 1 →
      (IsMaxOn (fun g => g ⬝ᵥ ((L⁻¹ * M) *ᵥ g)) {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = 1} f →
          ∃ μ : ℝ, M *ᵥ f = μ • f) ∧
      (IsMinOn (fun g => g ⬝ᵥ ((L⁻¹ * M) *ᵥ g)) {g | g ⬝ᵥ (L⁻¹ *ᵥ g) = 1} f →
          ∃ μ : ℝ, M *ᵥ f = μ • f) := by sorry

end NetworkVolatility.Robust
