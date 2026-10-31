-- Prove2me | Theorems.Thm_HuberSNSDP_lemma_6
-- name    : HuberSNSDP.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:08.899604+00:00
-- url     : https://prove2.me/theorems/b1c9925c-8319-46c1-9415-6da566c4000e
-- title:
--   Lemma 6 — $\hat{\mathcal E}'$ is nonsingular near every point with $\epsilon>0$
-- statement:
--   Let $\kappa_p,\kappa_c>0$ and let $\hat{\mathcal E}(\epsilon,X,y,Z)=(\epsilon;\mathcal E(\epsilon,X,y,Z))$ be the smoothed KKT map (18)–(19) of the SDP (1). For any $(\epsilon',X',y',Z')\in\mathbb R_{++}\times\mathbb X$ there is an open neighbourhood $\mathcal U$ of $(\epsilon',X',y',Z')$ such that
--   $$\hat{\mathcal E}'(\epsilon,X,y,Z)\ \text{is nonsingular for every }(\epsilon,X,y,Z)\in\mathcal U\text{ with }\epsilon>0.$$
--
--   This makes the Newton system (24) uniquely solvable at every iterate, so the inexactness condition (25) can always be met.
--
--   Differences from the source:
--   - encoding: $\mathbb S^n$, $\mathbb R^m$, $\mathbb X=\mathbb S^n\times\mathbb R^m\times\mathbb S^n$ with the trace inner product and Euclidean norms → `SymMat (Fin n)` (Frobenius inner product = trace inner product), `EuclideanSpace ℝ (Fin m)`, `WithLp 2` products; reason: Lean convention; the same spaces, inner products and norms
--   - encoding: the standing assumption of p.2 (an optimal solution of (1) exists and Slater's condition holds), stated once for the whole paper → the explicit hypothesis `D.Standing`; reason: the paper assumes it throughout ("In this paper, we assume", p.2)
--   - encoding: a linear map is nonsingular → `Function.Bijective` of the continuous linear map; reason: finite-dimensional spaces of equal dimension; same meaning
-- source:
--   Liang, Sun & Toh, A Squared Smoothing Newton Method for Semidefinite Programming, arXiv:2303.05825v4, Lemma 6, p.14

import Mathlib
import Definitions.Def_HuberSNSDP_Algorithm

open scoped RealInnerProductSpace Topology
open Filter SunNLSDP.Equiv NonsmoothNewton.Shared

namespace HuberSNSDP

/-- Lemma 6, p.14 (Liang, Sun & Toh, arXiv:2303.05825v4).

For any `(ε′, X′, y′, Z′) ∈ ℝ₊₊ × 𝕏` there is an open neighbourhood `𝒰` of `(ε′, X′, y′, Z′)` such
that `ℰ̂′(ε, X, y, Z)` is nonsingular for every `(ε, X, y, Z) ∈ 𝒰` with `ε > 0`.

**Formalization Note.** "Nonsingular" is bijectivity of the linear map `fderiv ℝ ℰ̂ w`; the
standing assumption of p.2 and `κp, κc > 0` (18) are hypotheses. -/
theorem lemma_6 {n m : ℕ} (D : SDPData n m) (hD : D.Standing) (kp kc : ℝ) (hkp : 0 < kp)
    (hkc : 0 < kc) (w' : ISpace n m) (hw' : 0 < epsOf w') :
    ∃ U : Set (ISpace n m), IsOpen U ∧ w' ∈ U ∧
      ∀ w ∈ U, 0 < epsOf w → Function.Bijective (fderiv ℝ (D.Ehat kp kc) w) := by sorry

end HuberSNSDP
