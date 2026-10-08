-- Prove2me | Theorems.Thm_LeightonRao_Product_lemma_10
-- name    : LeightonRao.Product.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:09.501614+00:00
-- url     : https://prove2.me/theorems/3daf029f-bc78-4aa6-b348-925bdecb8b55
-- title:
--   Lemma 10, p. 802 — if π(T) ≥ 2p/3 and Σ_{u∈𝒫−T} π(u)d(T,u) ≥ 1/2p, there is a cut of weighted ratio cost ≤ 6W
-- statement:
--   Let $G$ be a connected capacitated network on $V$, let $\pi\ge0$ be a PMFP node weighting with $p=|\mathcal P|\ge2$ and $\sum_u\pi(u)=p$, and let $d$ be a distance function with total weight $W$. Suppose $T\subseteq V$ satisfies $\pi(T)\ge 2p/3$ and
--   $$\sum_{u\in\mathcal P-T}\pi(u)\,d(T,u)\ge\frac1{2p}.$$
--   Then there is a cut $\langle U,\bar U\rangle$ with $\pi(U)>0$, $\pi(\bar U)>0$ and weighted ratio cost
--   $$\frac{C(U,\bar U)}{\pi(U)\pi(\bar U)}\le 6W.$$
--
--   This is the "heavy core" case of Lemma 11: when a heavy set $T$ is far, on average, from the remaining weight, a level cut around $T$ is cheap.
--
--   **Formalization Note** The page writes "ratio cost $O(W)$"; its proof (which defines $R_i$ as the *weighted* ratio cost) and its use in Lemma 11 make clear that the weighted ratio cost is meant, and that is what is stated. The constant $6$ is the one obtained by the computation in the proof of Lemma 5 (p. 800), to which the proof of Lemma 10 refers. The sum over $\mathcal P-T$ is written over $V\setminus T$; the extra terms vanish because $\pi=0$ off $\mathcal P$. Connectivity makes the graph distances $d(T,u)$ meaningful.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 802, Lemma 10 (constant from the proof of Lemma 5, p. 800)

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem lemma_10 {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (hconn : IsConnectedNet N)
    (π : V → ℝ) (hπ : IsPMFPWeight π) (hp : 2 ≤ (support π).card) (d : V → V → ℝ)
    (hd : IsDistanceFunction d) (T : Finset V)
    (hT : 2 * ((support π).card : ℝ) ≤ 3 * piSum π T)
    (hsum : 1 / (2 * ((support π).card : ℝ)) ≤ ∑ u ∈ Tᶜ, π u * distFrom N d T u) :
    ∃ U : Finset V, 0 < piSum π U ∧ 0 < piSum π Uᶜ ∧
      weightedRatio N π U ≤ 6 * totalWeight N d := by sorry

end LeightonRao.Product
