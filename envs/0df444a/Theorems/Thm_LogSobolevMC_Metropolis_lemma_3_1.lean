-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_lemma_3_1
-- name    : LogSobolevMC.Metropolis.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:25.530206+00:00
-- url     : https://prove2.me/theorems/056ad89a-d6b8-41aa-bac7-c4868642bdbe
-- title:
--   Lemma 3.1, p. 715 — 2α ≤ λ for any chain
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with an invariant probability $\pi$ charging every point. Its log-Sobolev constant $\alpha$ and spectral gap $\lambda$ satisfy
--
--   $$2\alpha\le\lambda.$$
--
--   Together with a lower bound on $\alpha$ obtained otherwise, this caps the log-Sobolev constant by the spectral gap; in Example 3.3 it turns the bound $\alpha(P)\ge 1/n$ and the known gap $\lambda(P)=2/n$ into the equality $\alpha(P)=1/n$.
--
--   **Formalization Note** The page's section assumes irreducibility; the statement does not need it and is stated without it (a stronger statement). On a one-point space both sides are $0$ in Lean.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 715, Lemma 3.1

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Lemma 3.1, p. 715: for any finite chain `K` with positive invariant probability `π`,
the log-Sobolev constant and the spectral gap satisfy `2α ≤ λ`. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π ≤ LogSobolevMC.ChiSquare.gap K π := by sorry

end LogSobolevMC.Metropolis
