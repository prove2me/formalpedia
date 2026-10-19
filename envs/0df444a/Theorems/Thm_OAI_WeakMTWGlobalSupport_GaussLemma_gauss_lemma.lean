-- Prove2me | Theorems.Thm_OAI_WeakMTWGlobalSupport_GaussLemma_gauss_lemma
-- name    : OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:56:46.105819+00:00
-- url     : https://prove2.me/theorems/620d0f40-b5ac-413f-8a3c-d99f80402636
-- title:
--   Gauss lemma for the flow of the geodesic spray in coordinates
-- statement:
--   **Setting.** $E$ is a finite-dimensional real inner product space, used as a coordinate space. $G : E \to \mathrm{Bil}(E)$ assigns to each point a continuous bilinear form $G_x$. On an open set $S$, $G$ is $C^\infty$, symmetric and positive definite, so it is a Riemannian metric in coordinates. Its Christoffel map is
--   $$\Gamma_x(v, v) = G_x^{-1}\Bigl(\tfrac12\bigl(DG_x(v)(v, \cdot) + DG_x(v)(v, \cdot) - DG_x(\cdot)(v, v)\bigr)\Bigr),$$
--   with $G_x^{-1}$ the inverse of $G_x : E \to E^*$ (`ContinuousLinearMap.inverse`). The geodesic spray is the vector field $(x, v) \mapsto (v, -\Gamma_x(v, v))$ on $E \times E$, whose integral curves are the geodesics with their velocities. $\Phi : \mathbb R \times (E \times E) \to E \times E$ is a local flow of the spray: it is $C^\infty$ on an open set $U$, $\Phi(0, q) = q$, and $t \mapsto \Phi(t, q)$ solves the spray equation with values over $S$.
--
--   **Statement.** Let $T \ge 0$ with $[0, T] \times \{(x, v)\} \subseteq U$. Write $\partial_v$ and $\partial_w$ for the derivatives of the position component of $\Phi(T, (x, \cdot\,))$ in the directions $v$ and $w$ of the initial velocity. Then, for every $w \in E$,
--   $$G_{\Phi(T,(x,v))_1}\bigl(\partial_v,\ \partial_w\bigr) = T^2\, G_x(v, w).$$
--
--   So the derivative of the exponential map preserves the inner product with the radial direction. This is the Gauss lemma of Riemannian geometry (Gauss 1827), stated for a flow of the geodesic spray in coordinates. The spray is written out explicitly, so the statement uses only Mathlib. Lean: `OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma`. It is OpenAI's theorem `flow_gauss` (in `lean/OAI/Geometry/WeakMTW/Geodesics/GaussLemma.lean`), with OpenAI's `geodesicSpray`, `christoffel` and `lowerChristoffel` unfolded.
-- source:
--   Gauss, Disquisitiones generales circa superficies curvas (1827); Lean: OpenAI, Global Support and Convex Injectivity Domains under Weak MTW, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 360; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/paper.pdf; Apache License 2.0), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakMTW/Geodesics/GaussLemma.lean (declaration OAI.WeakMTWGlobalSupport.GaussLemma.flow_gauss)

import Mathlib

open Set Filter InnerProductSpace
open scoped Topology ContDiff

theorem OAI.WeakMTWGlobalSupport.GaussLemma.gauss_lemma
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {G : E → (E →L[ℝ] E →L[ℝ] ℝ)} {S : Set E}
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ x ∈ S, ∀ v w, G x v w = G x w v)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < G x v v)
    {U : Set (ℝ × (E × E))} {Φ : ℝ × (E × E) → E × E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, (Φ q).1 ∈ S ∧
      HasDerivAt (fun t => Φ (t, q.2))
        ((Φ q).2, -((G (Φ q).1).inverse ((1 / 2 : ℝ) •
          (fderiv ℝ G (Φ q).1 (Φ q).2 (Φ q).2 + fderiv ℝ G (Φ q).1 (Φ q).2 (Φ q).2 -
            ((fderiv ℝ G (Φ q).1).flip (Φ q).2).flip (Φ q).2)))) q.1)
    {x v : E} {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) T, (t, (x, v)) ∈ U) (w : E) :
    G (Φ (T, (x, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, v))).1
      (fderiv ℝ Φ (T, (x, v)) (0, (0, w))).1 = T ^ 2 * G x v w := by
  sorry
