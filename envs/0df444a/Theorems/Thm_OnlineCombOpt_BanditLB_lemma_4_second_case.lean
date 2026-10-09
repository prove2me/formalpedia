-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_lemma_4_second_case
-- name    : OnlineCombOpt.BanditLB.lemma_4_second_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:45.030558+00:00
-- url     : https://prove2.me/theorems/40635d78-981f-4650-83b9-ce52f43e9543
-- title:
--   Lemma 4, second case, p. 21 — corrected bound KL(ℬ,ℬ′) ≤ (p′−p)²/((1−p)p′(n+2)) for q = p > p′
-- statement:
--   Let $n\ge1$ and $n/2\le\ell\le n$. Take $p,p'\in(0,1)$ with $p'<p$, and $r\in(0,1)$ when $\ell<n$. Let $\mathcal B$ be the law of a sum of $n+1$ independent Bernoulli variables with parameters $p$, then $\ell$ copies of $p$, then $n-\ell$ copies of $r$, and let $\mathcal B'$ be the same with the first parameter replaced by $p'$. Then
--
--   $$
--   \mathrm{KL}(\mathcal B,\mathcal B')\le\frac{(p'-p)^2}{(1-p)\,p'\,(n+2)}.
--   $$
--
--   This is the second case ($q=p$) of Lemma 4 in the configuration $p'<p$, which is the one used in Appendix B ($p=1/2$, $p'=1/2-\epsilon$). It gives the one-round bound of Appendix B for every $0<\epsilon<1/2$.
--
--   **Formalization Note** The paper's proof of this case (p. 21) applies Lemma 5 with $x_0=(1-p')/(1-p)$, which lies outside $(0,1)$ when $p'<p$, and concludes $\mathrm{KL}\le(p'-p)^2/(2(1-p')(\ell+1)p)$; the printed Lemma 4 is false in this configuration. The statement here is the corrected conclusion, obtained from the same argument with $x_0=p'/p$ (the minimum of Lemma 5's argument when $p'<p$) and $\ell+1\ge(n+2)/2$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 21, proof of Lemma 4, second case (display after "Finally, from Lemma 5 and (15)"), corrected

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem lemma_4_second_case (n ℓ : ℕ) (p p' r : ℝ)
    (hn : 1 ≤ n) (hhalf : n ≤ 2 * ℓ) (hℓ : ℓ ≤ n)
    (hp : 0 < p ∧ p < 1) (hp' : 0 < p' ∧ p' < 1)
    (hr : ℓ < n → 0 < r ∧ r < 1) (hlt : p' < p) :
    klFin (pbLaw (bernoulliParams n ℓ p p r))
      (pbLaw (bernoulliParams n ℓ p' p r)) ≤
      (p' - p)^2 / ((1 - p) * p' * (n + 2)) := by sorry

end OnlineCombOpt.BanditLB
