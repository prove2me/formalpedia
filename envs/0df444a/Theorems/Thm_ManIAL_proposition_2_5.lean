-- Prove2me | Theorems.Thm_ManIAL_proposition_2_5
-- name    : ManIAL.proposition_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:12:23.069053+00:00
-- url     : https://prove2.me/theorems/856ec80f-8f1e-4544-81d3-c55dda8c4c70
-- title:
--   Proposition 2.5 — gradient, Lipschitz constant and bounds of the Moreau envelope
-- statement:
--   Let $h:\mathbb R^m\to\mathbb R$ be convex and $\ell_h$-Lipschitz, and let $\mu>0$. Write $M_h^\mu(x)=\inf_z\{h(z)+\frac1{2\mu}\|z-x\|^2\}$ for the Moreau envelope and $\operatorname{prox}_{\mu h}(x)=\arg\min_y\{h(y)+\frac1{2\mu}\|y-x\|^2\}$ for the proximal operator. Then:
--
--   1. for every $x$ the minimizer $\operatorname{prox}_{\mu h}(x)$ exists and is unique;
--   2. $M_h^\mu$ is differentiable at every $x$, and with $p=\operatorname{prox}_{\mu h}(x)$
--   $$
--   \nabla M_h^\mu(x)=\frac1\mu\big(x-p\big)\in\partial h(p),\qquad \|\nabla M_h^\mu(x)\|\le\ell_h,\qquad \|x-p\|\le\mu\ell_h ;
--   $$
--   3. $\nabla M_h^\mu$ is Lipschitz continuous on $\mathbb R^m$ with constant $\mu^{-1}$.
--
--   This is what makes the augmented Lagrangian $\psi_k$ continuously differentiable with an explicit gradient (3.15), and it supplies the constants in Lemma 3.3 and in the feasibility bound (3.32).
--
--   **Formalization Note** $M_h^\mu$ is `moreauEnv (1/μ) h`; $p=\operatorname{prox}_{\mu h}(x)$ is the predicate `IsProxPoint h μ x p`, and the gradient formula is stated for every such $p$.
--
--   Differences from the source:
--   - generalization: prox_{µh}(x) := arg min (well-definedness implicit) → existence and uniqueness of the minimizer stated as conclusion 1; reason: an extra conclusion; the printed statements are conclusions 2–3
--   - encoding: h proper, convex, ℓh-Lipschitz on ℝⁿ → h : ℝᵐ → ℝ convex with |h y − h y'| ≤ ℓh‖y − y'‖, ℓh ≥ 0; reason: a real-valued h is proper; the space is named ℝᵐ as where h is used in (1.1)
--   - encoding: ∇M^µ_h(x) = (1/µ)(x − prox_{µh}(x)) → HasGradientAt (moreauEnv (1/µ) h) ((1/µ)(x − p)) x for every prox point p; reason: same statement; differentiability is part of HasGradientAt
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Proposition 2.5, displays (2.3)–(2.4), p.5

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_moreauEnv
import Definitions.Def_KallMayerSLP_KKT_subdifferential

open SAGA.StronglyConvex BnBPEP.WeakCvx

namespace ManIAL

/-- **Proposition 2.5** (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.5, citing [5, Lemma 3.3]). Let
`h : ℝᵐ → ℝ` be convex and `ℓ_h`-Lipschitz and `μ > 0`. Then
1. `prox_{μh}(x)` is well defined: for every `x` there is exactly one minimizer `p` of
   `h(·) + (1/2μ)‖· − x‖²`;
2. at every `x`, the Moreau envelope `M_h^μ` has gradient `(1/μ)(x − prox_{μh}(x))`, which lies in
   `∂h(prox_{μh}(x))` (2.3), and `‖∇M_h^μ(x)‖ ≤ ℓ_h`, `‖x − prox_{μh}(x)‖ ≤ μℓ_h` (2.4);
3. `∇M_h^μ` is Lipschitz on `ℝᵐ` with constant `μ⁻¹`.

**Formalization Note.** `M_h^μ` is `moreauEnv (1/μ) h` (`inf_z h(z) + (1/2μ)‖z − ·‖²`) and
`p = prox_{μh}(x)` is `IsProxPoint h μ x p`. A real-valued `h` is proper, and a Lipschitz `h` is
continuous, so it is closed (Definition 2.4). Lipschitz constants are nonnegative. -/
theorem proposition_2_5 {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → ℝ) (ℓh : ℝ) (hℓh : 0 ≤ ℓh)
    (hh : ConvexOn ℝ Set.univ h) (hhL : ∀ y y', |h y - h y'| ≤ ℓh * ‖y - y'‖)
    (μ : ℝ) (hμ : 0 < μ) :
    (∀ x, ∃! p, IsProxPoint h μ x p) ∧
    (∀ x p, IsProxPoint h μ x p →
      HasGradientAt (moreauEnv (1 / μ) h) ((1 / μ) • (x - p)) x ∧
      (1 / μ) • (x - p) ∈ KallMayerSLP.KKT.subdifferential h p ∧
      ‖(1 / μ) • (x - p)‖ ≤ ℓh ∧ ‖x - p‖ ≤ μ * ℓh) ∧
    (∀ x x', ‖gradient (moreauEnv (1 / μ) h) x - gradient (moreauEnv (1 / μ) h) x'‖ ≤
      μ⁻¹ * ‖x - x'‖) := by sorry

end ManIAL
