-- Prove2me | Theorems.Thm_GPSAnalysis_Core_mesh_separation
-- name    : GPSAnalysis.Core.mesh_separation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:37:47.938276+00:00
-- url     : https://prove2.me/theorems/2c4e1c2e-27b5-4419-9336-db3d44311400
-- title:
--   Lemma 3.2 — distinct mesh points are at least $\Delta_k/\|G^{-1}\|$ apart
-- statement:
--   Let $D=G\bar Z$ with $G\in\mathbb R^{n\times n}$ nonsingular and $\bar Z$ an integer $n\times p$ matrix, and let $M_k=\{x_k+\Delta_k Dz: z\in\mathbb Z_+^p\}$ be the mesh (2.4) with $\Delta_k>0$. Let $\|\cdot\|$ be any norm on $\mathbb R^n$ for which every nonzero integer vector has norm at least $1$, and let $\|G^{-1}\|$ be the operator norm it induces. Then
--
--   $$\min_{u\ne v\in M_k}\|u-v\|\ \ge\ \frac{\Delta_k}{\|G^{-1}\|}.$$
--
--   This separation of mesh points is the source of all mesh-refinement results of the paper: an iterate sequence confined to a compact set cannot move on coarse meshes forever.
--
--   **Formalization Note** The norm is given as an additive group norm $N$ that is absolutely homogeneous. Instead of the operator norm itself, the statement is made for every constant $c$ with $N(G^{-1}v)\le c\,N(v)$ for all $v$, with conclusion $N(u-v)\ge\Delta_k/c$ for distinct mesh points $u,v$; since $\|G^{-1}\|$ is the least such $c$, this is equivalent to the lemma. The mesh is stated for an arbitrary centre $x_k$ and parameter $\Delta_k>0$.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 895, Lemma 3.2

import Mathlib
import Definitions.Def_GPSAnalysis_Core_Mesh

open Matrix

namespace GPSAnalysis.Core

/-- Lemma 3.2 (Audet–Dennis 2003, p. 895). Let `N` be a norm on `ℝⁿ` for which every nonzero
integer vector has norm at least `1`, and let `c` bound the operator norm of `G⁻¹` induced by `N`
(`N(G⁻¹ v) ≤ c N(v)` for all `v`; the least such `c` is `‖G⁻¹‖`). Then any two distinct points
of the mesh `M_k` (2.4) built from `D = G Z̄` are at `N`-distance at least `Δ_k / c`. -/
theorem mesh_separation {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (hG : IsUnit G.det)
    (Zbar : Matrix (Fin n) (Fin p) ℤ) (xk : Fin n → ℝ) (Δk : ℝ) (hΔk : 0 < Δk)
    (N : AddGroupNorm (Fin n → ℝ)) (hN_smul : ∀ (a : ℝ) (v : Fin n → ℝ), N (a • v) = |a| * N v)
    (hN_int : ∀ z : Fin n → ℤ, z ≠ 0 → 1 ≤ N (fun i => (z i : ℝ)))
    (c : ℝ) (hc : ∀ v : Fin n → ℝ, N (G⁻¹ *ᵥ v) ≤ c * N v) :
    ∀ u ∈ mesh (dirMatrix G Zbar) xk Δk, ∀ v ∈ mesh (dirMatrix G Zbar) xk Δk,
      u ≠ v → Δk / c ≤ N (u - v) := by sorry

end GPSAnalysis.Core
