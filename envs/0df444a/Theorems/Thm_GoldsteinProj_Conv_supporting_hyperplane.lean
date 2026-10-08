-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_supporting_hyperplane
-- name    : GoldsteinProj.Conv.supporting_hyperplane
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:24:19.660003+00:00
-- url     : https://prove2.me/theorems/318dc9b6-337e-41c1-b703-b1c5c5b9b223
-- title:
--   Proof of (iii), p. 710 — [ρ_k∇f_k, z − x_{k+1}] ≧ [x_k − x_{k+1}, z] + [x_{k+1}, x_{k+1} − x_k] for z ∈ C
-- statement:
--   Let $H$ be a real Hilbert space with inner product $[\cdot,\cdot]$, $C \subseteq H$ convex, $P$ the projection onto $C$, and $f : H \to \mathbb R$. Let $(x_k)$ be a run of the gradient projection method, $x_{k+1} = P(x_k - \rho_k \nabla f(x_k))$, and write $\nabla f_k = \nabla f(x_k)$. Then for every $k$ and every $z \in C$,
--   $$[\rho_k \nabla f_k,\; z - x_{k+1}] \;\ge\; [x_k - x_{k+1},\; z] + [x_{k+1},\; x_{k+1} - x_k].$$
--
--   The inequality holds because $x_k - \rho_k \nabla f_k - x_{k+1}$ is either a normal to $C$ at $x_{k+1}$ or zero. It is the supporting-hyperplane step of the proofs of (iii) and (v).
--
--   **Formalization Note** Only the recursion of the run is used; the step-size window, the start and every hypothesis on $f$ are irrelevant here and are not assumed.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 710, PROOF, proof of (iii), fourth sentence

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 710, proof of (iii): along a gradient projection run, for every `z ∈ C`,
`⟪ρ_k ∇f(x_k), z - x_{k+1}⟫ ≥ ⟪x_k - x_{k+1}, z⟫ + ⟪x_{k+1}, x_{k+1} - x_k⟫`. -/
theorem supporting_hyperplane {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (x0 : H) (σ ρ0 : ℝ) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    ∀ k, ∀ z ∈ C,
      ⟪x k - x (k + 1), z⟫ + ⟪x (k + 1), x (k + 1) - x k⟫ ≤ ⟪ρ k • gradient f (x k), z - x (k + 1)⟫ := by sorry

end GoldsteinProj.Conv
