-- Prove2me | Theorems.Thm_OnlineCRS_Matching_product_formula
-- name    : OnlineCRS.Matching.product_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:28.458402+00:00
-- url     : https://prove2.me/theorems/6d6361cb-fec4-43da-8c2e-b273fd8a0c0a
-- title:
--   Proof of Theorem 2.7, p. 13 — Pr[g′ ∈ K, A ∩ K ∩ D = ∅] = q_{g′} · e^{−Σ_{g∈D} x_g}
-- statement:
--   Let $G=(V,E)$ be a finite loopless graph, let $x\in[0,1]^E$, and let $g'\in E$ have ends $u,v$; put $D=(\delta(u)\cup\delta(v))\setminus\{g'\}$. Let $A\sim R(x)$ and, independently, let $K$ contain every edge $g$ independently with probability $q_g(x)$, where $q_g(x)=(1-e^{-x_g})/x_g$ for $x_g>0$ and $q_g(x)=1$ for $x_g=0$. Then
--
--   $$\Pr\big[g'\in K,\ A\cap K\cap D=\varnothing\big]=q_{g'}(x)\cdot e^{-\sum_{g\in D}x_g}.$$
--
--   The identity holds because every edge lies in $A\cap K$ independently with probability $x_g\,q_g(x)=1-e^{-x_g}$; it turns the selectability probability into an exponential of the weight around $g'$.
--
--   **Formalization Note** The probability is the double finite sum over $K$ and $A$ of the product weights. For $x_{g'}>0$ the right side is the paper's $\frac{1-e^{-x_{g'}}}{x_{g'}}e^{-\sum_{g\in D}x_g}$; the case $x_{g'}=0$, where the paper's ratio is undefined, uses the limit value $q=1$.
-- source:
--   arXiv:1508.00142v2, proof of Theorem 2.7, p. 13, sentence before the display and the display's first two lines

import Mathlib
import Definitions.Def_OnlineCRS_Matching_Model

namespace OnlineCRS.Matching

/-- Proof of Theorem 2.7, p. 13: independence gives the displayed product formula. -/
theorem product_formula {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (x : E → ℝ)
    (hx : ∀ g, 0 ≤ x g ∧ x g ≤ 1) (g : E) (u v : V)
    (hg : G.ends g = s(u, v)) :
    (∑ K : Finset E, ∑ A : Finset E,
      OnlineCRS.Matroid.activeProb (incl x) K * OnlineCRS.Matroid.activeProb x A *
        (if g ∈ K ∧ A ∩ K ∩ otherIncident G u v g = ∅ then (1 : ℝ) else 0)) =
      incl x g * Real.exp (-(∑ h ∈ otherIncident G u v g, x h)) := by sorry

end OnlineCRS.Matching
