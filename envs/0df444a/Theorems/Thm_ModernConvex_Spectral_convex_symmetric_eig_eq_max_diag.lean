-- Prove2me | Theorems.Thm_ModernConvex_Spectral_convex_symmetric_eig_eq_max_diag
-- name    : ModernConvex.Spectral.convex_symmetric_eig_eq_max_diag
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:31.702124+00:00
-- url     : https://prove2.me/theorems/e1977017-3df9-4178-9b02-c149581c940d
-- title:
--   (D) — f(λ(A)) is the maximum of f(Dg(VᵀAV)) over orthogonal V
-- statement:
--   Let $f : \mathbb R^m \to \mathbb R$ be convex and symmetric (invariant under permutations of the coordinates). For a square matrix $B$ let $\operatorname{Dg}(B) = (B_{11},\dots,B_{mm})$ be its diagonal. Let $\mathcal O_m$ be the set of orthogonal $m\times m$ matrices. Then for every symmetric $m\times m$ matrix $A$,
--   $$f(\lambda(A)) = \max_{V \in \mathcal O_m} f\big(\operatorname{Dg}(V^TAV)\big),$$
--   and the maximum is attained.
--
--   The result turns a convex symmetric function of the eigenvalues into a maximum of convex functions of the matrix entries. This exhibits $A \mapsto f(\lambda(A))$ as convex.
--
--   **Formalization Note** $f$ is real-valued and convex on all of $\mathbb R^m$ ("a symmetric convex function on $\mathbf R^m$"). The equality with an attained maximum is stated as: $f(\lambda(A))$ is the greatest element of $\{f(\operatorname{Dg}(V^TAV)) : V^TV = I\}$. For square $V$, $V^TV = I$ is orthogonality.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 282, fact (D)

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix

namespace ModernConvex.Spectral

/-- Ben-Tal–Nemirovski, fact (D), p. 282: let `f` be a symmetric convex function on `ℝᵐ`. Then
for every symmetric `m × m` matrix `A`, `f(λ(A)) = max_{V ∈ 𝒪_m} f(Dg(VᵀAV))`, where `𝒪_m` is
the set of `m × m` orthogonal matrices and `Dg` is the diagonal; the maximum is attained. -/
theorem convex_symmetric_eig_eq_max_diag {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hsym : IsSymmetricFn f) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ V : Matrix (Fin m) (Fin m) ℝ, Vᵀ * V = 1 ∧ r = f (diag (Vᵀ * A * V))}
      (f (eigVec A)) := by sorry

end ModernConvex.Spectral
