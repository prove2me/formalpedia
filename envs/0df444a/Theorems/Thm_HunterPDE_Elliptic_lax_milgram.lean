-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_lax_milgram
-- name    : HunterPDE.Elliptic.lax_milgram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:47:07.9948+00:00
-- url     : https://prove2.me/theorems/dc0e6979-444e-4022-96cc-d0c06fc89dae
-- title:
--   Theorem 4.20 — Lax–Milgram theorem
-- statement:
--   Let $\mathcal{H}$ be a real Hilbert space and $a : \mathcal{H}\times\mathcal{H} \to \mathbb{R}$ a bilinear form. Assume there are constants $C_1, C_2 > 0$ with
--   $$C_1\|u\|^2 \le a(u,u), \qquad |a(u,v)| \le C_2\|u\|\,\|v\| \qquad \text{for all } u, v \in \mathcal{H}.$$
--   Then for every bounded linear functional $f : \mathcal{H} \to \mathbb{R}$ there is a unique $u \in \mathcal{H}$ with $\langle f, v\rangle = a(u,v)$ for all $v \in \mathcal{H}$.
--
--   This extends the Riesz representation theorem to non-symmetric forms and is the tool that turns energy estimates into existence of weak solutions.
--
--   **Formalization Note.** `a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ` is only assumed bilinear; its boundedness is a hypothesis. The notes give no proof ("For the proof, see [9]").
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 103, Theorem 4.20

import Mathlib

namespace HunterPDE.Elliptic

/-- Theorem 4.20 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 103 (Lax–Milgram): let `H` be
a real Hilbert space and `a : H × H → ℝ` a bilinear form on `H`. Assume there are constants
`C₁, C₂ > 0` with `C₁ ‖u‖² ≤ a(u, u)` and `|a(u, v)| ≤ C₂ ‖u‖ ‖v‖` for all `u, v ∈ H`. Then for
every bounded linear functional `f : H → ℝ` there is a unique `u ∈ H` with `⟨f, v⟩ = a(u, v)`
for all `v ∈ H`. The form is only assumed bilinear; its boundedness is the hypothesis `ha₂`. -/
theorem lax_milgram {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a : H →ₗ[ℝ] H →ₗ[ℝ] ℝ) (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (ha₁ : ∀ u : H, C₁ * ‖u‖ ^ 2 ≤ a u u) (ha₂ : ∀ u v : H, |a u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (f : StrongDual ℝ H) :
    ∃! u : H, ∀ v : H, f v = a u v := by sorry

end HunterPDE.Elliptic
