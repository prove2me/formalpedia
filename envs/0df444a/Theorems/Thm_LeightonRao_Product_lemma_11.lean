-- Prove2me | Theorems.Thm_LeightonRao_Product_lemma_11
-- name    : LeightonRao.Product.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:57.155034+00:00
-- url     : https://prove2.me/theorems/95b88665-60a9-40a0-a0ce-f6b227db3ae6
-- title:
--   Lemma 11, p. 803 — a distance function meeting the weighted distance constraint yields a cut of weighted ratio cost ≤ 36W log p
-- statement:
--   Let $G$ be a connected capacitated network on $V$, let $\pi\ge0$ be a PMFP node weighting with $p=|\mathcal P|\ge2$ and $\sum_u\pi(u)=p$, and let $d$ be a distance function with total weight $W$ satisfying the weighted distance constraint
--   $$\sum_{\{u,v\}\in\mathcal P^2}\pi(u)\pi(v)\,d(u,v)\ge1.$$
--   Then there is a cut $\langle U,\bar U\rangle$ with $\pi(U)>0$, $\pi(\bar U)>0$ and
--   $$\frac{C(U,\bar U)}{\pi(U)\pi(\bar U)}\le 36\,W\log_2 p .$$
--
--   Combined with LP duality ($W=f$ for an optimal distance function) this gives $\mathcal S\le 36 f\log p$, the lower half of Theorem 7.
--
--   **Formalization Note** The page states $O(W\log p)$. The constant $36$ bounds both branches of the proof: Corollary 9's $36W\log p$ and Lemma 10's $6W$, since $\log_2 p\ge1$ for $p\ge2$. The normalization $\sum\pi=p$ is the standing assumption of §2.3; connectivity makes graph distances meaningful.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 803, Lemma 11

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lemma_11 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (hdc : SatisfiesPMFPConstraint N π d) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 36 * totalWeight N d * Real.logb 2 ((support π).card : ℝ) := by sorry

end LeightonRao.Product
