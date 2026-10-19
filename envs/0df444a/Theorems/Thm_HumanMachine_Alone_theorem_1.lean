-- Prove2me | Theorems.Thm_HumanMachine_Alone_theorem_1
-- name    : HumanMachine.Alone.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:16.619354+00:00
-- url     : https://prove2.me/theorems/7261064b-38b1-4338-b1bf-d9c0f4db4555
-- title:
--   Theorem 1 — the optimal choice probability in closed form
-- statement:
--   For every information cost $\lambda>0$, let $\underline\mu=1/(e^{1/\lambda}+1)$ and $\overline\mu=e^{1/\lambda}/(e^{1/\lambda}+1)$. For every prior $0<\mu<1$, every strategy that maximizes expected accuracy less entropy cost has the unconditional probability $p^\star$ of choosing the good-state action given by
--
--   $$
--   p^\star(\mu)=\begin{cases}
--   0,&\mu\le\underline\mu,\\
--   \dfrac{\mu}{1-e^{-1/\lambda}}-\dfrac{1-\mu}{e^{1/\lambda}-1},&\underline\mu<\mu<\overline\mu,\\
--   1,&\mu\ge\overline\mu.
--   \end{cases}
--   $$
--
--   The thresholds satisfy $\underline\mu<1/2<\overline\mu$. For fixed $\lambda$, the optimal probability is non-decreasing in $\mu$ on $(0,1)$. As $\lambda$ increases over positive values, $\underline\mu$ increases strictly and $\overline\mu$ decreases strictly.
--
--   This is the baseline choice rule used in the paper's later machine-input comparisons.
--
--   **Formalization Note** Optimality is over every pair of conditional choice probabilities in $[0,1]^2$, using the paper's §4 reduction of problem (2). The closed-form function is only the right-hand side of the theorem, not the definition of an optimal probability. The printed wording “that solves (4), (5) and (6)” is read in the context of the optimal decision problem; those equations alone also admit endpoint solutions.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 12 (PDF p. 13), Theorem 1, equation (11), and p. 32 (PDF p. 33), proof.

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

namespace HumanMachine.Alone

theorem theorem_1 :
    (∀ lam : ℝ, 0 < lam →
      (∀ mu : ℝ, mu ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ pg pb : ℝ, IsOptimal lam mu pg pb → choiceProb mu pg pb = pClosed lam mu) ∧
      muLow lam < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < muHigh lam ∧
      MonotoneOn (pClosed lam) (Set.Ioo (0 : ℝ) 1)) ∧
    StrictMonoOn muLow (Set.Ioi (0 : ℝ)) ∧
    StrictAntiOn muHigh (Set.Ioi (0 : ℝ)) := by sorry

end HumanMachine.Alone
