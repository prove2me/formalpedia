-- Prove2me | Theorems.Thm_NewsBundling_Unilateral_lemma2_attention
-- name    : NewsBundling.Unilateral.lemma2_attention
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:06:45.080159+00:00
-- url     : https://prove2.me/theorems/45be78cb-5a02-4d88-a302-3c231a8fb390
-- title:
--   Lemma 2, p. 11 — allocation of consumer attention
-- statement:
--   Given news quality $q\in[0,1]$ and a platform news share $0\le\lambda<1$, let $T_1\in[0,1]$ be the consumer's time on the newspaper website. The consumer's utility-maximizing allocation is unique and satisfies
--
--   $$T_1(q,\lambda)=\max\!\left\{\frac{q-\lambda}{1-\lambda},0\right\}.$$
--
--   This is the final-stage choice used in the platform's and newspaper's problems.
--
--   **Formalization Note** The formula is stated as an equivalence with the consumer best-response predicate, including feasibility and optimality.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 11, Lemma 2

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

namespace NewsBundling.Unilateral

/-- Lemma 2, p. 11: the unique consumer best response for q in [0,1] and 0 ≤ λ < 1. -/
theorem lemma2_attention :
    ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      ∀ T1 : ℝ, IsConsumerBR q lam T1 ↔
        T1 = max ((q - lam) / (1 - lam)) 0 := by sorry

end NewsBundling.Unilateral
