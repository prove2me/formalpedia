-- Prove2me | Theorems.Thm_KleinbergHITS_Conv_iterate_closed_form
-- name    : KleinbergHITS.Conv.iterate_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:08.155932+00:00
-- url     : https://prove2.me/theorems/7804c82e-902b-45d6-a425-844c4d9f87a5
-- title:
--   §3, proof of Theorem 3.1, p. 10 — x_k is the unit vector along (AᵀA)^{k−1}Aᵀz and y_k the unit vector along (AAᵀ)^k z
-- statement:
--   Let $A$ be the adjacency matrix of a directed graph on $n$ pages, $z=(1,\dots,1)\in\mathbb R^n$, and let $(x_k,y_k)$ be the output of the procedure Iterate$(G,k)$: $x_0=y_0=z$, and for $i\ge1$, $x_i'=\mathcal I(y_{i-1})$, $y_i'=\mathcal O(x_i')$, and $x_i$, $y_i$ are $x_i'$, $y_i'$ normalized so that their squares sum to $1$. Write $\mathrm{unit}(w)=w/\|w\|_2$ for the unit vector in the direction of $w$. Then for every $k\ge1$,
--   $$x_k=\mathrm{unit}\big((A^{\top}A)^{k-1}A^{\top}z\big),\qquad y_k=\mathrm{unit}\big((AA^{\top})^{k}z\big).$$
--
--   This identifies Kleinberg's iterates with normalized power iterates of the symmetric matrices $A^{\top}A$ and $AA^{\top}$, which is what allows the convergence theory of the power method to be applied.
--
--   **Formalization Note** The identity holds for every graph, with no use of Assumption (†). "The unit vector in the direction of $w$" is the mission's `normalize w`, which returns $0$ when $w=0$; both sides then vanish together, so the statement does not rely on that convention to be true, but it is part of its meaning when an iterate is $0$. The restriction $k\ge1$ is needed: at $k=0$ the iterate $x_0$ is $z$, not the unit vector along $A^{\top}z$.
-- source:
--   Kleinberg, Authoritative sources in a hyperlinked environment, J. ACM 46(5) (1999), author's copy, p. 10, §3, proof of Theorem 3.1 ("Thus x_k is the unit vector in the direction of (AᵀA)^{k−1}Aᵀz, and y_k is the unit vector in the direction of (AAᵀ)^k z")

import Mathlib
import Definitions.Def_KleinbergHITS_Conv_Setting

namespace KleinbergHITS.Conv

open Matrix

/-- Kleinberg (1999), §3, proof of Theorem 3.1, p. 10: "Thus x_k is the unit vector in the direction
of (AᵀA)^{k−1}Aᵀz, and y_k is the unit vector in the direction of (AAᵀ)^k z." Stated for `k ≥ 1`. -/
theorem iterate_closed_form {n : ℕ} (E : Fin n → Fin n → Prop) [DecidableRel E] :
    ∀ k : ℕ, 1 ≤ k →
      (hitsIter E k).1 =
          normalize ((((adjMatrix E)ᵀ * adjMatrix E) ^ (k - 1)) *ᵥ ((adjMatrix E)ᵀ *ᵥ allOnes n)) ∧
        (hitsIter E k).2 = normalize (((adjMatrix E * (adjMatrix E)ᵀ) ^ k) *ᵥ allOnes n) := by sorry

end KleinbergHITS.Conv
