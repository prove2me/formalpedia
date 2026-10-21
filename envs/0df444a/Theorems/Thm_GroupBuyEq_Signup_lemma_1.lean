-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_lemma_1
-- name    : GroupBuyEq.Signup.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:36.695964+00:00
-- url     : https://prove2.me/theorems/e3f82e2b-3bff-48e2-8c65-149718e95c03
-- title:
--   Lemma 1, p. 9 — a customer signs up iff u ≥ ū ∈ [p₂, p₀], with ū given by the three-branch formula (3)
-- statement:
--   Consider the two-threshold group-buying model with deposit $d>0$, deal discount $\delta\ge0$ and prices $p_0$, $p_1=p_0-\delta$, $p_2=p_1-\delta$. Let $a,b\ge0$ with $a+b\le1$ be the probabilities that only the first deal, resp. the second deal, happens after a customer arriving at time $t$ with $N_t=k$ joins (that is, $a=\pi^1_{k+1}(t)$ and $b=\pi^2_{k+1}(t)$). Let $V(a,b,u)$ be the expected utility (1) of signing up and $\bar u(a,b)$ the threshold of (3).
--
--   Then $\bar u(a,b)\in[p_2,p_0]$, and for every reservation utility $u$,
--   $$V(a,b,u)\ge0\iff u\ge\bar u(a,b).$$
--
--   That is, the customer signs up (which he does exactly when $V\ge0$) if and only if his utility exceeds the explicit threshold $\bar u$. This is the threshold structure of the sign-up decision on which the equilibrium characterization of Proposition 1 rests.
--
--   **Formalization Note** The page writes the first branch of (3) as "$0\le d\le\delta\pi^2_{k+1}(t)$"; the lemma is stated under the model's standing assumption $d>0$ (p. 7), because at $d=0$ every customer has $V\ge0$ and the equivalence fails. The simplex conditions $a,b\ge0$, $a+b\le1$ are implicit on the page ($a,b$ are probabilities of disjoint events). The model's $\delta\ge0$ (p. 7) is assumed instead of Proposition 1's stronger $0<\delta<p_0/2$.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), p. 9 (PDF 10), Lemma 1, (3)

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem lemma_1 (P : Params) (hd : 0 < P.d) (hδ : 0 ≤ P.δ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (P.p2 ≤ ubar P a b ∧ ubar P a b ≤ P.p0) ∧ ∀ u : ℝ, 0 ≤ V P a b u ↔ ubar P a b ≤ u := by sorry

end GroupBuyEq.Signup
