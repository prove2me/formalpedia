-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_lemma_4
-- name    : OnlineCombOpt.BanditLB.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:33.312784+00:00
-- url     : https://prove2.me/theorems/e3a32c26-4c61-4cbb-83a4-a11e3d1dab37
-- title:
--   Lemma 4, p. 20 — corrected KL bound for Bernoulli sums
-- statement:
--   Let $n\ge1$ and $n/2\le\ell\le n$. Take $p,p',q\in(0,1)$ with $q\in\{p,p'\}$, and take $r\in(0,1)$ when $\ell<n$. Let $B$ sum $n+1$ independent Bernoulli variables with parameters $p$, then $\ell$ copies of $q$, then $n-\ell$ copies of $r$. Define $B'$ by replacing only $p$ with $p'$. Under the necessary additional condition $p(1-p')\le2p'(1-p)$,
--
--   $$
--   \mathrm{KL}(B,B')\le\frac{2(p'-p)^2}{(1-p')(n+2)q}.
--   $$
--
--   This is the divergence estimate used in the lower-bound argument.
--
--   **Formalization Note** The printed lemma omits the odds condition and is false: $n=\ell=1$, $p=q=1/2$, $p'=0.001$ is a counterexample. The condition repairs the statement. The paper's phrase “$1/2\le n/2$” is represented by $n\ge1$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 20, Lemma 4; p. 21, second case of proof

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem lemma_4 (n ℓ : ℕ) (p p' q r : ℝ)
    (hn : 1 ≤ n) (hhalf : n ≤ 2 * ℓ) (hℓ : ℓ ≤ n)
    (hp : 0 < p ∧ p < 1) (hp' : 0 < p' ∧ p' < 1)
    (hq : 0 < q ∧ q < 1) (hr : ℓ < n → 0 < r ∧ r < 1)
    (hchoice : q = p ∨ q = p')
    (hodds : p * (1 - p') ≤ 2 * p' * (1 - p)) :
    klFin (pbLaw (bernoulliParams n ℓ p q r))
      (pbLaw (bernoulliParams n ℓ p' q r)) ≤
      2 * (p' - p)^2 / ((1 - p') * (n + 2) * q) := by sorry

end OnlineCombOpt.BanditLB
