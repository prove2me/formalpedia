-- Prove2me | Theorems.Thm_LeightonRao_Product_theorem_7
-- name    : LeightonRao.Product.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:08.853976+00:00
-- url     : https://prove2.me/theorems/3283accb-b691-4d2f-99ac-b79ebd2a5621
-- title:
--   Theorem 7, pp. 801–802 — for every product multicommodity flow problem with k commodities, Ω(𝒮/log k) ≤ f ≤ 𝒮
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $G$ be a connected capacitated network on a finite vertex set $V$, and let $\pi\ge0$ be a node weighting with $p\ge2$ nodes of positive weight, normalized so that $\sum_{u\in V}\pi(u)=p$. Consider the product multicommodity flow problem in which every pair $\{u,v\}$ of nodes has demand $\pi(u)\pi(v)$; it has $k=\binom p2$ commodities with nonzero demand. Let $f$ be its (concurrent) max-flow and
--   $$\mathcal S=\min_{U:\ \pi(U)>0,\ \pi(\bar U)>0}\frac{C(U,\bar U)}{\pi(U)\pi(\bar U)}$$
--   its min-cut. Then
--   $$\frac{c\,\mathcal S}{\log_2\max(k,2)}\le f\le\mathcal S .$$
--
--   The upper bound is weak duality; the lower bound says the gap between the multicommodity max-flow and min-cut for product demands is at most logarithmic in the number of commodities. The uniform problem ($\pi\equiv1$) is the special case $p=n$. The paper's proof gives $c=1/36$.
--
--   **Formalization Note** The page's $\Omega(\cdot)$ is one constant $c$ for all instances, so $\exists c$ precedes every quantifier. For $p=2$ there is $k=1$ commodity and $\log k=0$; the bound is stated with $\log_2\max(k,2)$, which changes nothing for $k\ge2$. Demands are encoded on ordered pairs, $\tfrac12\pi(u)\pi(v)$ each way (footnote 7). The min-cut ranges over cuts with $\pi(U)\pi(\bar U)>0$. The normalization $\sum\pi=p$ is the paper's "without loss of generality" of §2.3, kept as a hypothesis; connectivity is the standing assumption of p. 789.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 801–802, Theorem 7

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem theorem_7 : ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ),
      IsConnectedNet N → IsPMFPWeight π → 2 ≤ (support π).card →
      c * pmfpMinCut N π / Real.logb 2 ((max (numCommodities π) 2 : ℕ) : ℝ) ≤
          maxFlow N (productDemand π) ∧
        maxFlow N (productDemand π) ≤ pmfpMinCut N π := by sorry

end LeightonRao.Product
