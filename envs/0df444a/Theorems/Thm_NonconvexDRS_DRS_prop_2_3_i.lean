-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_prop_2_3_i
-- name    : NonconvexDRS.DRS.prop_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:45:50.055709+00:00
-- url     : https://prove2.me/theorems/7d763e9d-09b8-49d8-b3ce-e767006b4a85
-- title:
--   Proposition 2.3(i), p. 7 — for L-smooth σ-hypoconvex h and γ < 1/[σ]₋, h is prox-bounded and prox_{γh} is single-valued with s = u + γ∇h(u)
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$ be $L_h$-smooth and $\sigma_h$-hypoconvex with $\sigma_h\in[-L_h,L_h]$. Then:
--
--   1. $h$ is prox-bounded with threshold $\gamma_h\ge 1/[\sigma_h]_-$: for every $0<\gamma<1/[\sigma_h]_-$ the function $h+\frac1{2\gamma}\|\cdot\|^2$ is bounded below;
--   2. for every such $\gamma$ and every $s\in\mathbb R^n$, the proximal mapping $\operatorname{prox}_{\gamma h}(s)$ consists of exactly one point, and
--   $$u=\operatorname{prox}_{\gamma h}(s)\iff s=u+\gamma\nabla h(u).$$
--
--   This identifies the first DRS step with the inverse of $\mathrm{id}+\gamma\nabla\varphi_1$ and underlies the change of variables $s\leftrightarrow u$ used throughout the analysis.
--
--   **Formalization Note** The page writes $h\in C^{1,1}(\operatorname{dom}h)$; since $h$ is real-valued this is $C^{1,1}(\mathbb R^n)$. The bound $\gamma<1/[\sigma_h]_-$ is written $\gamma[\sigma_h]_-<1$ (no constraint when $\sigma_h\ge0$). Single-valuedness is unique existence of an element of the set `proxSet`.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 7, Proposition 2.3(i)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Proposition 2.3 (i), p. 7. -/
theorem prop_2_3_i {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (Lh σh : ℝ)
    (hsmooth : IsLSmooth h Lh) (hσ : -Lh ≤ σh ∧ σh ≤ Lh) (hhypo : IsHypoconvex h σh) :
    (∀ γ : ℝ, 0 < γ → γ * negPartR σh < 1 → ∃ m : ℝ, ∀ x, m ≤ h x + ‖x‖ ^ 2 / (2 * γ)) ∧
    ∀ γ : ℝ, 0 < γ → γ * negPartR σh < 1 → ∀ s : EuclideanSpace ℝ (Fin n),
      (∃! u, u ∈ proxSet (fun x => (h x : EReal)) γ s) ∧
      ∀ u, u ∈ proxSet (fun x => (h x : EReal)) γ s ↔ s = u + γ • gradient h u := by sorry

end NonconvexDRS.DRS
