-- Prove2me | Theorems.Thm_LeightonRao_Product_corollary_9
-- name    : LeightonRao.Product.corollary_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:02.042004+00:00
-- url     : https://prove2.me/theorems/8800dcc3-7ab5-4a47-8c77-eca21a9a06a0
-- title:
--   Corollary 9, p. 802 — either a component T of radius 1/2p² with π(T) ≥ 2p/3, or a cut of weighted ratio cost ≤ 36W log p
-- statement:
--   Let $G$ be a capacitated network on $V$, let $\pi\ge0$ be a PMFP node weighting with $p=|\mathcal P|\ge2$ nodes of positive weight and $\sum_u\pi(u)=p$, and let $d$ be a distance function with total weight $W$. Then at least one of the following holds:
--
--   1. there is a vertex set $T$ of radius at most $1/(2p^2)$ with $\pi(T)\ge 2p/3$;
--   2. there is a cut $\langle U,\bar U\rangle$ with $\pi(U)>0$, $\pi(\bar U)>0$ and weighted ratio cost
--   $$\frac{C(U,\bar U)}{\pi(U)\pi(\bar U)}\le 36\,W\log_2 p .$$
--
--   Either outcome feeds Lemma 11: the cut finishes the argument directly, and the heavy small-radius set $T$ is the input of Lemma 10.
--
--   **Formalization Note** The page states the bound as $O(W\log p)$. The constant $36$ is the one obtained by the computation in the proof of Corollary 4 (p. 799), to which the proof of Corollary 9 refers: $\Delta=1/(2p^2)$ in Lemma 8 gives cross capacity $8Wp^2\log p$, and two sides of weight at least $p/3$ each give $\pi(U)\pi(\bar U)\ge 2p^2/9$. "Find a component" is formalized as the existence of a vertex set with the stated radius and weight. The normalization $\sum\pi=p$ is the standing assumption of §2.3.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 802, Corollary 9 (constant from the proof of Corollary 4, p. 799)

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem corollary_9 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ)
    (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) :
    (∃ T : Finset V, 2 * ((support π).card : ℝ) ≤ 3 * piSum π T ∧
        HasRadiusLE N d T (1 / (2 * ((support π).card : ℝ) ^ 2))) ∨
    (∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
        weightedRatio N π U ≤
          36 * totalWeight N d * Real.logb 2 ((support π).card : ℝ)) := by sorry

end LeightonRao.Product
