-- Prove2me | Theorems.Thm_HumanMachine_Alone_lemma_1
-- name    : HumanMachine.Alone.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:13.524073+00:00
-- url     : https://prove2.me/theorems/44714138-d101-4f92-930f-d62372a30410
-- title:
--   Lemma 1 — optimal conditional choice probabilities
-- statement:
--   Let $\lambda>0$ and $0<\mu<1$. For any pair $(p_g,p_b)$ maximizing expected accuracy less cognitive cost over $[0,1]^2$, write $p=\mu p_g+(1-\mu)p_b$. The optimal conditional probabilities obey
--
--   $$
--   p_g=\frac{pe^{1/\lambda}}{pe^{1/\lambda}+1-p},\qquad
--   p_b=\frac{p}{p+(1-p)e^{1/\lambda}}.
--   $$
--
--   These are equations (5) and (6) of Lemma 1 and link the optimization problem to the choice probability analyzed in Theorem 1.
--
--   **Formalization Note** The printed phrase “unique solution” is false for equations (4)–(6) alone: both endpoint probabilities solve them. Equation (4) is the definition of $p$, while equations (7) and (8) are the definitions of accuracy and cost in the §4 reduction. This statement asserts only what every optimizer satisfies. The reduction is adopted from Matějka and McKay (2015), not proved here.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 11 (PDF p. 12), Lemma 1, equations (4)–(8); proof p. 32 (PDF p. 33).

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Alone

theorem lemma_1 (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hopt : IsOptimal lam mu pg pb) :
    let p := choiceProb mu pg pb
    pg = p * Real.exp (1 / lam) / (p * Real.exp (1 / lam) + 1 - p) ∧
      pb = p / (p + (1 - p) * Real.exp (1 / lam)) := by sorry

end HumanMachine.Alone
