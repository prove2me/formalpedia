-- Prove2me | Theorems.Thm_LeightonRao_Product_weak_duality
-- name    : LeightonRao.Product.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:21:46.429102+00:00
-- url     : https://prove2.me/theorems/89b0f864-c0a1-4085-a1c7-2c8392ed4434
-- title:
--   §1.2, pp. 789–790 — PMFP weak duality: every concurrent flow value f satisfies f·π(U)π(Ū) ≤ C(U, Ū)
-- statement:
--   Let $G$ be a capacitated network on a finite vertex set $V$, let $\pi:V\to\mathbb R$ be a node weighting, and consider the product multicommodity flow problem in which each ordered pair $u\neq v$ is a commodity with demand $\tfrac12\pi(u)\pi(v)$. If a concurrent flow of value $\lambda$ exists, then for every cut $\langle U,\bar U\rangle$ with $\pi(U)>0$ and $\pi(\bar U)>0$,
--   $$\lambda\,\pi(U)\,\pi(\bar U)\le C(U,\bar U).$$
--
--   The demand separated by $U$ is $D(U,\bar U)=\pi(U)\pi(\bar U)$, so this is the paper's observation that $f\le C(U,\bar U)/D(U,\bar U)$, i.e. the max-flow is at most the min-cut. It gives the upper half $f\le\mathcal S$ of Theorem 7.
--
--   **Formalization Note** The paper states the observation for an arbitrary multicommodity flow problem; here it is specialized to the product demands of §2.3.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), pp. 789–790, §1.2, paragraph after the min-cut definition (max-flow upper bounded by min-cut), applied to the PMFP of §2.3, p. 801

import Mathlib
import Definitions.Def_LeightonRao_Product_Setting

namespace LeightonRao.Product

theorem weak_duality {V : Type} [Fintype V] [DecidableEq V] (N : Network V) (π : V → ℝ)
    (f : V → V → V → V → ℝ) (lam : ℝ) (hf : IsConcurrentFlow N (productDemand π) f lam)
    (U : Finset V) (hU : 0 < piSum π U) (hUc : 0 < piSum π Uᶜ) :
    lam * (piSum π U * piSum π Uᶜ) ≤ cutCap N U := by sorry

end LeightonRao.Product
