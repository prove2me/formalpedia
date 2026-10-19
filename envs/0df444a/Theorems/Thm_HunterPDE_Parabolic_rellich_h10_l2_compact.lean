-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_rellich_h10_l2_compact
-- name    : HunterPDE.Parabolic.rellich_h10_l2_compact
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:25:14.393652+00:00
-- url     : https://prove2.me/theorems/d4ae989b-a7a8-4f53-b5bc-0128c73b3708
-- title:
--   Rellich: for bounded open $\Omega$ the embedding $H^1_0(\Omega)\hookrightarrow L^2(\Omega)$ is compact
-- statement:
--   Let $\Omega\subset\mathbb{R}^n$ be bounded and open. Then the inclusion
--
--   $$\iota: H^1_0(\Omega)\to L^2(\Omega),\qquad u\mapsto u,$$
--
--   is a compact operator: every bounded sequence in $H^1_0(\Omega)$ has a subsequence that converges in $L^2(\Omega)$.
--
--   Role: compactness of $H^1_0(\Omega)\hookrightarrow L^2(\Omega)$ makes the solution operator of the Dirichlet problem a compact self-adjoint operator on $L^2(\Omega)$, whose eigenfunctions give the orthonormal basis $\{w_k\}$ of Dirichlet eigenfunctions used for the Galerkin approximations (6.15)–(6.16) in the proof of Theorem 6.3.
--
--   **Formalization Note**: $H^1_0(\Omega)$ is the published closure of the jets of $C_c^\infty(\Omega)$ in $L^2(\Omega;\mathbb{R}\times\mathbb{R}^n)$ and $\iota$ is the published `toL2L` (first component of the jet); compactness is Mathlib's `IsCompactOperator`. For $W^{1,p}_0$ no regularity of $\partial\Omega$ is needed.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), doi:10.1090/gsm/019, §5.7, Theorem 1 (Rellich–Kondrachov Compactness Theorem) and the remark after it (W^{1,p}_0(U) ⊂⊂ L^p(U) for bounded open U, no C^1 boundary needed), p. 286; used for the Dirichlet eigenbasis (6.15) in Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, proof of Theorem 6.3, p. 181

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10

namespace HunterPDE.Parabolic

theorem rellich_h10_l2_compact {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) : IsCompactOperator (toL2L n Ω) := by sorry

end HunterPDE.Parabolic
