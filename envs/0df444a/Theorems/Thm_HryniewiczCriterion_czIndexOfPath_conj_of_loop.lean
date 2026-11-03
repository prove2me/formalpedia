-- Prove2me | Theorems.Thm_HryniewiczCriterion_czIndexOfPath_conj_of_loop
-- name    : HryniewiczCriterion.czIndexOfPath_conj_of_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T17:51:21.122611+00:00
-- url     : https://prove2.me/theorems/b7e9b4aa-5404-474b-b7ca-a4077fd6428f
-- title:
--   The Conley–Zehnder index of a nondegenerate path is unchanged by a change of frame along a loop of winding zero
-- statement:
--   Let $\varphi:[0,1]\to\mathrm{Sp}(1)=\mathrm{SL}(2,\mathbb{R})$ be continuous with $\varphi(0)=I$ and $\det(I-\varphi(1))\neq0$. Let $G:[0,1]\to\mathrm{Sp}(1)$ be continuous with $G(1)=G(0)$, and assume that the loop $t\mapsto G(t)G(0)^{-1}e_1$ has winding number zero around the origin: there are a continuous $\theta:[0,1]\to\mathbb{R}$ with $\theta(1)=\theta(0)$ and $r(t)>0$ with
--   $$G(t)G(0)^{-1}e_1=r(t)\,(\cos\theta(t),\sin\theta(t))\qquad(t\in[0,1]).$$
--   Then Hryniewicz's index of the path $t\mapsto G(t)\,\varphi(t)\,G(0)^{-1}$ equals that of $\varphi$:
--   $$\mu\big(G\varphi G(0)^{-1}\big)=\mu(\varphi).$$
--
--   This is the invariance of the Conley–Zehnder index of a nondegenerate path under a change of symplectic trivialization by a loop that is contractible in $\mathrm{Sp}(1)$. It is used to compare the index of a periodic orbit computed in one global frame with the index computed in another frame along the orbit.
--
--   **Formalization Note** $\mu$ is `HryniewiczCriterion.czIndexOfPath` (closed form of $\hat\mu$ of the winding interval). Paths are maps `ℝ → Matrix (Fin 2) (Fin 2) ℝ`; only their values on $[0,1]$ matter, and continuity is `ContinuousOn` on `Set.Icc 0 1`. Membership in $\mathrm{Sp}(1)$ is stated as determinant $1$, and $e_1$ and $(\cos\theta,\sin\theta)$ are `rotationVector 0` and `rotationVector θ`.
-- source:
--   J. Gutt, The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728, Proposition 8; U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.1.1

import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open HryniewiczCriterion

/-- Let `φ : [0, 1] → Sp(1)` be continuous with `φ(0) = I` and `1` not an eigenvalue of `φ(1)`,
and let `G : [0, 1] → Sp(1)` be continuous with `G(1) = G(0)` such that the loop
`t ↦ G(t) G(0)⁻¹ e₁` has winding number zero. Then `czIndexOfPath (G φ G(0)⁻¹) = czIndexOfPath φ`. -/
theorem HryniewiczCriterion.czIndexOfPath_conj_of_loop (φ G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hφc : ContinuousOn φ (Set.Icc 0 1)) (hφ0 : φ 0 = 1)
    (hφd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (φ t).det = 1) (hφ1 : (1 - φ 1).det ≠ 0)
    (hGc : ContinuousOn G (Set.Icc 0 1)) (hGd : ∀ t ∈ Set.Icc (0 : ℝ) 1, (G t).det = 1)
    (hG1 : G 1 = G 0) (θ : ℝ → ℝ) (hθc : ContinuousOn θ (Set.Icc 0 1)) (hθ1 : θ 1 = θ 0)
    (hθ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (rotationVector 0) = r • rotationVector (θ t)) :
    czIndexOfPath (fun t => G t * φ t * (G 0)⁻¹) = czIndexOfPath φ := by sorry
