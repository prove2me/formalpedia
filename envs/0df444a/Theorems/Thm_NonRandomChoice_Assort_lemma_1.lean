-- Prove2me | Theorems.Thm_NonRandomChoice_Assort_lemma_1
-- name    : NonRandomChoice.Assort.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:35.124542+00:00
-- url     : https://prove2.me/theorems/5b21be95-226f-43c2-978d-7ae51cad3139
-- title:
--   Lemma 1, p. 28 — choice probabilities convex in q_0 make a revenue-ordered assortment optimal
-- statement:
--   Let $\mathcal N=\{1,\dots,N\}$ be a set of products and let $q_i(S)$ be the probability that a consumer offered $S\subseteq\mathcal N$ chooses product $i$, with no-purchase probability $q_0(S)=1-\sum_{i\in S}q_i(S)$. Assume the choice model is **regular**: $q_i(S)\ge0$, $q_i(S)=0$ for $i\notin S$, $\sum_{i\in S}q_i(S)\le1$, and the choice probability of every product $i\in S$ and of the no-purchase option does not increase when the offer set is enlarged from $S$ to $S'\supseteq S$.
--
--   Suppose each choice probability can be written as a function of the no-purchase probability: for every product $i$ there are a convex set $D_i\subseteq\mathbb R$ and a function $f_i$ that is nonnegative and convex on $D_i$ such that, for every offer set $S$ containing $i$,
--   $$q_0(S)\in D_i\qquad\text{and}\qquad q_i(S)=f_i\bigl(q_0(S)\bigr).$$
--   Let the prices satisfy $p_1\ge p_2\ge\dots\ge p_N$ and let $S_n=\{1,\dots,n\}$ (with $S_0=\emptyset$). Then some revenue-ordered assortment is optimal for
--   $$\max_{S\subseteq\mathcal N}R(S),\qquad R(S)=\sum_{i\in S}p_i\,q_i(S),$$
--   that is, there is $n\in\{0,1,\dots,N\}$ with $R(S)\le R(S_n)$ for every $S\subseteq\mathcal N$.
--
--   This is the sufficient condition through which Theorem 5 is proved: it reduces optimality of revenue-ordered assortments to a convexity property of the choice probabilities as functions of $q_0$.
--
--   **Formalization Note** The model is the published regular discrete choice model `RevenueOrdered.Ratio.IsRegular` (products `Fin N`, the no-purchase option outside it), whose monotonicity includes the no-purchase option, as the paper's proof uses ("$q_0(S)$ is smaller by the regularity condition"). The page's "$q_i=q_i(q_0)$ is convex in $q_0$" is read as: $f_i$ convex and nonnegative on a set $D_i$ containing $q_0(S)$ for every $S\ni i$ (the representation only holds for offered products, since $q_i(S)=0$ off $S$; nonnegativity is what the proof's inequality (26) uses at $j\notin S^*$). The conclusion allows $n=0$ ($S_0=\emptyset$), which the proof uses as $S_{k-1}$ with $k=1$; no sign condition on prices is needed. "Revenue-order assortment" on the page is read as revenue-ordered. The paper's convex weight $\gamma$ does not appear in the statement.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), p. 28, Lemma 1, eq. (25)

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NonRandomChoice.Assort

theorem lemma_1 {N : ℕ} (P : Fin N → Finset (Fin N) → ℝ)
    (hP : RevenueOrdered.Ratio.IsRegular P) (p : Fin N → ℝ) (hp : Antitone p)
    (f : Fin N → ℝ → ℝ) (D : Fin N → Set ℝ)
    (hconv : ∀ i, ConvexOn ℝ (D i) (f i))
    (hnonneg : ∀ i, ∀ x ∈ D i, 0 ≤ f i x)
    (hrep : ∀ (S : Finset (Fin N)) (i : Fin N), i ∈ S →
      RevenueOrdered.Ratio.noPurchase P S ∈ D i ∧
        P i S = f i (RevenueOrdered.Ratio.noPurchase P S)) :
    ∃ n : ℕ, n ≤ N ∧ ∀ S : Finset (Fin N),
      RevenueOrdered.Ratio.revenue P p S ≤ RevenueOrdered.Ratio.revenue P p (roSet N n) := by sorry

end NonRandomChoice.Assort
