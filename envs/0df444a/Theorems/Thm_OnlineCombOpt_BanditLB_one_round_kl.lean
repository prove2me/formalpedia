-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_one_round_kl
-- name    : OnlineCombOpt.BanditLB.one_round_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:34.764207+00:00
-- url     : https://prove2.me/theorems/49097b4b-cf32-42db-ab7c-4dce6b867074
-- title:
--   Appendix B, p. 18 — KL bound for one observed loss
-- statement:
--   Let $m\ge1$ and $0<\epsilon<1/2$. Consider a sum $B'$ of $m$ independent Bernoulli variables, each with parameter $1/2$ or $1/2-\epsilon$. At an index whose parameter is $1/2-\epsilon$, replace that parameter by $1/2$ to obtain $B$. Then
--
--   $$
--   \mathrm{KL}(B,B')\le\frac{8\epsilon^2}{(1-4\epsilon^2)m}.
--   $$
--
--   The estimate bounds the information in one scalar bandit observation.
--
--   **Formalization Note** The conclusion includes $m=1$, which the printed Lemma 4 does not cover. For $\epsilon>1/6$ the printed Lemma 4 does not apply (it is false in this configuration, see the corrected second case); this one-round bound remains valid for every $0<\epsilon<1/2$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 18, Appendix B, display after “Now using Lemma 4”

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem one_round_kl (m : ℕ) (ε : ℝ) (p : Fin m → ℝ) (j₀ : Fin m)
    (hε : 0 < ε ∧ ε < (1 : ℝ) / 2)
    (hp : ∀ j, p j = (1 : ℝ) / 2 ∨ p j = (1 : ℝ) / 2 - ε)
    (hj : p j₀ = (1 : ℝ) / 2 - ε) :
    klFin (pbLaw (Function.update p j₀ ((1 : ℝ) / 2))) (pbLaw p) ≤
      8 * ε^2 / ((1 - 4 * ε^2) * m) := by sorry

end OnlineCombOpt.BanditLB
