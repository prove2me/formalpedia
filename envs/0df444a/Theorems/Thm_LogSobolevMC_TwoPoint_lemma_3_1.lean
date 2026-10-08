-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_lemma_3_1
-- name    : LogSobolevMC.TwoPoint.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:47.699987+00:00
-- url     : https://prove2.me/theorems/96f57085-339f-4779-93da-02e2d99abf67
-- title:
--   Lemma 3.1, p. 715 — 2α ≤ λ
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$ with invariant probability $\pi$, positive at every point. Let $\alpha$ be its log-Sobolev constant (3.1) and $\lambda$ its spectral gap (2.4). Then
--
--   $$2\alpha\le\lambda.$$
--
--   The log-Sobolev constant never exceeds half the spectral gap. In the proof of Theorem A.1 this bound identifies the case in which the infimum defining $\alpha$ is not attained at a nonconstant function.
--
--   **Formalization Note** The page states the lemma "for any chain K"; the irreducibility assumed at the start of §3.1 is not used, and is not a hypothesis here.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 715, Lemma 3.1

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Lemma 3.1 (p. 715): for any finite chain `K` with positive invariant probability `π`,
the log-Sobolev constant `α` and the spectral gap `λ` satisfy `2α ≤ λ`. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π ≤ LogSobolevMC.ChiSquare.gap K π := by sorry

end LogSobolevMC.TwoPoint
