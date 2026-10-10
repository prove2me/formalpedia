-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_prop_2_3_ii
-- name    : NonconvexDRS.DRS.prop_2_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:02.663604+00:00
-- url     : https://prove2.me/theorems/d702e2e2-e07e-40b1-bee6-d43ca5bfa451
-- title:
--   Proposition 2.3(ii), p. 7 — prox_{γh} is 1/(1+γL)-strongly monotone and (1+γσ)-cocoercive; the bounds (2.8); id + γ∇h is (1+γL)-Lipschitz
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$ be $L_h$-smooth and $\sigma_h$-hypoconvex with $\sigma_h\in[-L_h,L_h]$, and let $0<\gamma<1/[\sigma_h]_-$. For all $s,s'\in\mathbb R^n$, with $u=\operatorname{prox}_{\gamma h}(s)$ and $u'=\operatorname{prox}_{\gamma h}(s')$,
--   $$\langle u-u',s-s'\rangle\ge\frac1{1+\gamma L_h}\|s-s'\|^2\qquad\text{and}\qquad\langle u-u',s-s'\rangle\ge(1+\gamma\sigma_h)\|u-u'\|^2 .$$
--   In particular
--   $$\frac1{1+\gamma L_h}\|s-s'\|\le\|u-u'\|\le\frac1{1+\gamma\sigma_h}\|s-s'\|,\tag{2.8}$$
--   and $\|(u+\gamma\nabla h(u))-(u'+\gamma\nabla h(u'))\|\le(1+\gamma L_h)\|u-u'\|$.
--
--   These estimates transfer decrease and boundedness between the $s$-sequence and the $u$-sequence of DRS; the lower bound in (2.8) converts the decrease in $\|u-u^+\|$ into the decrease (4.2) in $\|s-s^+\|$.
--
--   **Formalization Note** $u$ and $u'$ are taken as arbitrary elements of the proximal sets (which are singletons by Proposition 2.3(i)). The bound $\gamma<1/[\sigma_h]_-$ is written $\gamma[\sigma_h]_-<1$. The last sentence of the page ("its inverse $\mathrm{id}+\gamma\nabla h$ is $(1+\gamma L_h)$-Lipschitz continuous") is the last conjunct.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 7, Proposition 2.3(ii), (2.8)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Proposition 2.3 (ii) and (2.8), p. 7. -/
theorem prop_2_3_ii {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (Lh σh : ℝ)
    (hsmooth : IsLSmooth h Lh) (hσ : -Lh ≤ σh ∧ σh ≤ Lh) (hhypo : IsHypoconvex h σh)
    (γ : ℝ) (hγ : 0 < γ) (hγσ : γ * negPartR σh < 1)
    (s s' u u' : EuclideanSpace ℝ (Fin n))
    (hu : u ∈ proxSet (fun x => (h x : EReal)) γ s)
    (hu' : u' ∈ proxSet (fun x => (h x : EReal)) γ s') :
    ⟪u - u', s - s'⟫_ℝ ≥ 1 / (1 + γ * Lh) * ‖s - s'‖ ^ 2 ∧
    ⟪u - u', s - s'⟫_ℝ ≥ (1 + γ * σh) * ‖u - u'‖ ^ 2 ∧
    1 / (1 + γ * Lh) * ‖s - s'‖ ≤ ‖u - u'‖ ∧
    ‖u - u'‖ ≤ 1 / (1 + γ * σh) * ‖s - s'‖ ∧
    ‖(u + γ • gradient h u) - (u' + γ • gradient h u')‖ ≤ (1 + γ * Lh) * ‖u - u'‖ := by sorry

end NonconvexDRS.DRS
