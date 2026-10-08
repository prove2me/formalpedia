-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_power_iteration_tendsto
-- name    : KleinbergHITS.Conv.power_iteration_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:19.302578+00:00
-- url     : https://prove2.me/theorems/d7eb143b-6fb9-4d7c-b0a2-df4a43001093
-- title:
--   §3, proof of Theorem 3.1, p. 11 — for symmetric M and v not orthogonal to ω₁(M), the unit vector along M^k v converges to ω₁(M)
-- statement:
--   Let $M$ be a real symmetric $n\times n$ matrix satisfying Assumption (†): its eigenvalue $\lambda_1$ of largest absolute value is simple and $|\mu|<|\lambda_1|$ for every other eigenvalue $\mu$. Assume moreover $\lambda_1>0$. Let $v\in\mathbb R^n$ be a vector that is not orthogonal to the principal eigenvector, i.e. $\langle v,\omega\rangle\ne0$ for a unit vector $\omega$ spanning the eigenspace of $\lambda_1$. Then there is a principal eigenvector $\omega_1$ of $M$ such that
--   $$\frac{M^k v}{\|M^k v\|_2}\;\longrightarrow\;\omega_1\qquad(k\to\infty).$$
--
--   This is the "standard result of linear algebra" that the proof of Theorem 3.1 invokes: the normalized power method converges to the dominant eigenvector from any start with a nonzero component along it.
--
--   **Formalization Note** Two disclosed deviations. (1) The hypothesis $\lambda_1>0$ is added. The page states no sign condition, and for $\lambda_1<0$ the vectors $M^kv/\|M^kv\|$ alternate in sign and do not converge; the two matrices the result is applied to, $AA^{\top}$ and $A^{\top}A$, are positive semidefinite, so their principal eigenvalue under (†) is positive and nothing is lost downstream. (2) The page says the limit is $\omega_1(M)$, a vector fixed by an arbitrary choice of sign; here the conclusion is that the limit is *a* principal eigenvector (it is $\pm\omega_1$, with the sign of $\langle v,\omega_1\rangle$). Not being orthogonal to a principal eigenvector does not depend on which of the two signs is used. The normalization is `normalize`, which divides by the Euclidean norm.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 11, §3, proof of Theorem 3.1, first sentence of the second paragraph ("a standard result of linear algebra (e.g. [30]) states that …")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix Filter Topology

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 11: if `M` is a symmetric `n × n` matrix and `v`
is not orthogonal to the principal eigenvector `ω₁(M)`, then the unit vector in the direction of
`M^k v` converges to a principal eigenvector of `M`. The principal eigenvalue is assumed positive
(the page's claim fails for a negative one; both matrices it is applied to are positive
semidefinite). -/
theorem power_iteration_tendsto {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (l₁ : ℝ) (hl : IsPrincipalEigenvalue M l₁) (hpos : 0 < l₁) (v : Fin n → ℝ)
    (hv : ∃ ω, IsPrincipalEigenvector M ω ∧ v ⬝ᵥ ω ≠ 0) :
    ∃ ω, IsPrincipalEigenvector M ω ∧
      Tendsto (fun k : ℕ => normalize ((M ^ k) *ᵥ v)) atTop (𝓝 ω) := by sorry

end KleinbergHITS.Conv
