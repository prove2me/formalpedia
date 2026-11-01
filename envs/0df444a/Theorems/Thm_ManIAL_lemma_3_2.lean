-- Prove2me | Theorems.Thm_ManIAL_lemma_3_2
-- name    : ManIAL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:01.292493+00:00
-- url     : https://prove2.me/theorems/c9598333-5c89-465d-850d-292528df1629
-- title:
--   Lemma 3.2 — iteration complexity of RGD
-- statement:
--   Let $\psi$ be retr-smooth on $\mathcal M$ with constant $L>0$ and a map $R$ that sends tangent vectors at points of $\mathcal M$ to points of $\mathcal M$, and let $m\le\psi$ on $\mathcal M$. Let $x_0\in\mathcal M$ and let $x_t$ be the iterates of Riemannian gradient descent $x_{t+1}=R_{x_t}(-\frac1L\operatorname{grad}\psi(x_t))$ (Algorithm 2). Then for every integer $T\ge1$ and every $t^*\in\arg\min_{0\le t\le T}\|\operatorname{grad}\psi(x_t)\|$,
--
--   $$
--   \|\operatorname{grad}\psi(x_{t^*})\|\le\frac{\sqrt{2L(\psi(x_0)-m)}}{\sqrt T}.
--   $$
--
--   With $m=\psi_{\min}=\inf_{\mathcal M}\psi$ this is the printed rate. It bounds the number of inner iterations ManIAL spends on each subproblem.
--
--   Differences from the source:
--   - generalization: ψ_min = inf_{x∈M} ψ(x) → any lower bound m of ψ on M; reason: m = ψ_min gives the printed bound
--   - generalization: R a retraction on a Riemannian submanifold M → M any set, R any map with R_x(u) ∈ M for x ∈ M, u ∈ T_xM; reason: the proof uses only (3.17) and that the iterates stay on M
--   - reading: Given an integer T; x∗ the output of Algorithm 2 → every integer T ≥ 1 and every argmin index t* ≤ T; reason: Algorithm 2 requires T > 0 and outputs an argmin; every tie-break is covered
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Lemma 3.2, p.10

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_rgrad
import Definitions.Def_ManIAL_IsRetrSmooth
import Definitions.Def_ManIAL_rgdSeq

open ProjLikeRetr.Retractor ZORiem.RGD

namespace ManIAL

/-- **Lemma 3.2** (Iteration complexity of RGD) (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.10).
Let `ψ` be retr-smooth on `M` with constant `L > 0` and retraction `R`, let `m ≤ ψ` on `M`, and
let `x_t` be the iterates of Algorithm 2 started at `x₀ ∈ M`. For every integer `T ≥ 1` and every
output index `t* ∈ argmin_{0 ≤ t ≤ T} ‖grad ψ(x_t)‖`,
`‖grad ψ(x_{t*})‖ ≤ √(2L(ψ(x₀) − m)) / √T`.

**Formalization Note.** The paper's `ψ_min = inf_M ψ` is replaced by any lower bound `m` of `ψ`
on `M` (with `m = ψ_min` this is the printed bound). Of the retraction only `R_x(u) ∈ M` for
`u ∈ T_xM` is used. -/
theorem lemma_3_2 {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hR : ∀ x ∈ M, ∀ u ∈ tangentSpace M x, R x u ∈ M)
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) (hL : 0 < L) (hψ : IsRetrSmooth M R ψ L)
    (mψ : ℝ) (hm : ∀ x ∈ M, mψ ≤ ψ x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ M) (T : ℕ) (hT : 1 ≤ T)
    (tstar : ℕ) (htT : tstar ≤ T)
    (hmin : ∀ s ≤ T, ‖rgrad M ψ (rgdSeq M R ψ L x₀ tstar)‖ ≤ ‖rgrad M ψ (rgdSeq M R ψ L x₀ s)‖) :
    ‖rgrad M ψ (rgdSeq M R ψ L x₀ tstar)‖ ≤
      Real.sqrt (2 * L * (ψ x₀ - mψ)) / Real.sqrt T := by sorry

end ManIAL
