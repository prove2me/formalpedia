-- Prove2me | Theorems.Thm_LeightonRao_Product_lp_duality
-- name    : LeightonRao.Product.lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:57.284979+00:00
-- url     : https://prove2.me/theorems/bee8ccaa-ba0b-481e-9804-128b40b44340
-- title:
--   §2.3, p. 802 with §2.2, p. 796 — PMFP LP duality: the minimum total weight of a distance function meeting the weighted distance constraint equals the max-flow
-- statement:
--   Let $G$ be a connected capacitated network on $V$, and let $\pi\ge0$ be a PMFP node weighting with $\sum_u\pi(u)=p$ and at least $p\ge2$ nodes of positive weight. Let $f$ be the max-flow of the product multicommodity flow problem. Then
--
--   1. every distance function $d$ satisfying the weighted distance constraint $\sum_{\{u,v\}\in\mathcal P^2}\pi(u)\pi(v)d(u,v)\ge1$ has total weight $W=\sum_{e}C(e)d(e)\ge f$, and
--   2. some distance function satisfying this constraint has total weight exactly
--   $$W=f.$$
--
--   This is the linear-programming duality between the concurrent flow problem and its distance dual, which the paper cites (Chvátal, Iri, Shahrokhi–Matula) and uses with the PMFP distance constraint of p. 802. It is the step "$W=f$" by which the cut bounds of Lemma 11 turn into the flow bound of Theorem 7.
--
--   **Formalization Note** The paper does not prove this; it invokes LP duality (§2.2, p. 796). The hypotheses $p\ge2$ and connectivity make the max-flow finite and positive. The normalization $\sum\pi=p$ is the standing assumption of §2.3.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 802, §2.3, the weighted distance constraint, with p. 796, §2.2, Eq. (4) and the LP duality sentence

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lp_duality {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) :
    (∀ d : V → V → ℝ, IsDistanceFunction d → SatisfiesPMFPConstraint N π d →
        maxFlow N (productDemand π) ≤ totalWeight N d) ∧
    (∃ d : V → V → ℝ, IsDistanceFunction d ∧ SatisfiesPMFPConstraint N π d ∧
        totalWeight N d = maxFlow N (productDemand π)) := by sorry

end LeightonRao.Product
