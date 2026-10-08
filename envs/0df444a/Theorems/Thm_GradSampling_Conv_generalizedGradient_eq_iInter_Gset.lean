-- Prove2me | Theorems.Thm_GradSampling_Conv_generalizedGradient_eq_iInter_Gset
-- name    : GradSampling.Conv.generalizedGradient_eq_iInter_Gset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:48:27.284086+00:00
-- url     : https://prove2.me/theorems/b07f30b7-eb00-49cf-a499-bdb25cb5ebdc
-- title:
--   §2, p. 754 — ∂̄f(x) = ⋂_{ε>0} G_ε(x)
-- statement:
--   Let $f$ be locally Lipschitz, $D$ open and dense with $D^c$ of Lebesgue measure zero, and $f$ continuously differentiable on $D$. Then for every $x\in\mathbb R^n$
--
--   $$\bar\partial f(x)=\bigcap_{\epsilon>0}G_\epsilon(x).$$
--
--   This representation is what lets gradients sampled at points of $D$ near $x$ approximate the Clarke subdifferential.
--
--   **Formalization Note** The hypothesis $\operatorname{vol}(D^c)=0$ is added. Without it the identity can fail: on $\mathbb R$, let $C$ be a closed nowhere dense set of positive measure, $D=C^c$ and $f(x)=\int_0^x\mathbf 1_C$. Then $f$ is $1$-Lipschitz and locally constant on $D$, so $G_\epsilon(x)=\{0\}$, while $f'(x)=1$ at every density point $x$ of $C$, so $1\in\bar\partial f(x)$ there.
-- source:
--   Burke, Lewis, Overton, A robust gradient sampling algorithm for nonsmooth, nonconvex optimization, SIAM J. Optim. 15 (2005), p. 754, §2, display after "representation of the Clarke subdifferential"

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_GradSampling_Conv_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace GradSampling.Conv

/-- §2, p. 754: `∂̄f(x) = ⋂_{ε>0} G_ε(x)`. The hypothesis `volume Dᶜ = 0` is added (see the
Formalization Note): with an open dense `D` of non-null complement the identity can fail. -/
theorem generalizedGradient_eq_iInter_Gset {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : LocallyLipschitz f)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hDo : IsOpen D) (hDd : Dense D)
    (hC1 : ContDiffOn ℝ 1 f D)
    (hDnull : volume Dᶜ = 0) :
    ∀ x, ClarkeGradients.Shared.generalizedGradient f x = ⋂ (ε : ℝ) (_ : 0 < ε), Gset f D ε x := by sorry

end GradSampling.Conv
