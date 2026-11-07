-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_5
-- name    : IterRoundDet.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:15.358944+00:00
-- url     : https://prove2.me/theorems/9b8d8968-3e90-4446-8b33-e51881427c5c
-- title:
--   Lemma 3.5 — entropy curvature: $\nabla^2E_p=-C^\dagger$ on $T_F$, and $C$ is a graph Laplacian
-- statement:
--   Let $a\in P(\mathcal N)$, let $F$ be the minimal face of $P(\mathcal N)$ containing $a$, let $T_F=\{y:a\pm ty\in F\text{ for some }t>0\}$ be its tangent space, and let $C=\mathbb E_{\mu_a}[(\mathbf 1_S-a)(\mathbf 1_S-a)^\top]$ be the covariance of the maximizing distribution. Then $\operatorname{range}C=T_F$,
--
--   $$v^\top\nabla^2E_p(a)v=-v^\top C^\dagger v\qquad(v\in T_F),$$
--
--   and
--
--   $$0\preceq C\preceq\operatorname{diag}(a),\quad C_{ii}=a_i(1-a_i),\quad C_{ij}\le 0\ (i\ne j),\quad C\mathbf 1=0.$$
--
--   In particular $C$ is a graph Laplacian. The curvature identity is what the second-order improvement step exploits.
--
--   **Formalization Note** The Hessian is stated as the second derivative at $0$ of $t\mapsto E_p(a+tv)$, together with $C^2$ regularity at $0$, since $a$ may lie on the boundary of $P(\mathcal N)$ and only directions in $T_F$ make sense.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
--   - encoding: v⊤∇²E_p(a)v on T_F → deriv (deriv φ) 0 with φ(t) = E_p(a + t v), plus ContDiffAt ℝ 2 φ 0; reason: the Hessian is meaningful only along T_F, where the line stays in F; ContDiffAt guards the junk value of deriv
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.5, p.14; proof pp.32–35

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation
import Definitions.Def_IterRoundDet_Covariance

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.5 (Entropy Curvature), p.14. Let `a ∈ P(N)`, `F` the minimal face of `P(N)` containing `a`,
`T_F` its tangent space, and `C = E_{μ_a}[(1_S − a)(1_S − a)⊤]` the covariance of the maximizing distribution
`μ_a`. Then `range C = T_F`; `v⊤∇²E_p(a)v = −v⊤C†v` for `v ∈ T_F`, (18); `0 ⪯ C ⪯ diag(a)`, `C_ii = a_i(1 − a_i)`,
`C_ij ≤ 0` for `i ≠ j`, `C1 = 0`. In particular `C` is a graph Laplacian matrix.

**Formalization Note.** `∇²E_p(a)` is only meaningful along `T_F`, since `a` may lie on the boundary of `P(N)`.
So (18) is stated on the line `t ↦ E_p(a + t v)`, which stays in `F` for small `|t|`, and `ContDiffAt ℝ 2` guards the
junk value of `deriv`. -/
theorem lemma_3_5 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c) {a : Fin n → ℝ}
    (ha : a ∈ supportPolytope c) {μ : Finset (Fin n) → ℝ} (hμ : IsMaxEnt c a μ) :
    (LinearMap.range (Matrix.mulVecLin (covMat μ a)) : Set (Fin n → ℝ)) =
      tangentAt (supportPolytope c) a ∧
    (∀ v ∈ tangentAt (supportPolytope c) a,
      ContDiffAt ℝ 2 (fun t : ℝ => Ep c (a + t • v)) 0 ∧
      deriv (deriv fun t : ℝ => Ep c (a + t • v)) 0 = -pinvForm (covMat μ a) v) ∧
    (covMat μ a).PosSemidef ∧
    (Matrix.diagonal a - covMat μ a).PosSemidef ∧
    (∀ i, covMat μ a i i = a i * (1 - a i)) ∧
    (∀ i j, i ≠ j → covMat μ a i j ≤ 0) ∧
    (covMat μ a).mulVec (fun _ => 1) = 0 ∧
    IsGraphLaplacian (covMat μ a) := by sorry

end IterRoundDet
