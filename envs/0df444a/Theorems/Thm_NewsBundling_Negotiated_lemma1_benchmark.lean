-- Prove2me | Theorems.Thm_NewsBundling_Negotiated_lemma1_benchmark
-- name    : NewsBundling.Negotiated.lemma1_benchmark
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:08.862812+00:00
-- url     : https://prove2.me/theorems/94446ce8-7179-481c-87da-74b269e64246
-- title:
--   Lemma 1, p. 10 — without content bundling the equilibrium quality is q̂ = β/c and the publisher's profit π̂₁ = β²/(2c)
-- statement:
--   Assume the standing assumptions of Table 1: $\varphi_0,\varphi_1\in(0,1)$, $\beta>\varphi_1$, $c>2\beta$, $\Lambda\in(0,1/2)$. In the benchmark without content bundling (the baseline game with $\Lambda=0$) a subgame-perfect equilibrium exists, and in every one the quality and the publisher's profit are
--
--   $$\hat q=\frac{\beta}{c},\qquad \hat\pi_1=\frac{\beta^2}{2c}.$$
--
--   This is the benchmark that part 1 of Proposition 5 compares with.
--
--   **Formalization Note** This restates, in the namespace `NewsBundling.Negotiated`, the same statement as the companion mission on unilateral content bundling. $\Lambda$ appears only in the hypothesis; the game is played at cap $0$.
-- source:
--   de Cornière & Sarvary, Social Media and News: Content Bundling and News Quality, TSE Working Paper n° 1152 (August 2021), p. 10, §4.1, Lemma 1

import Mathlib
import Definitions.Def_NewsBundling_Negotiated_Setting

namespace NewsBundling.Negotiated

theorem lemma1_benchmark (β φ0 φ1 c Λ : ℝ) (h : NewsBundling.Unilateral.StandingAssumptions β φ0 φ1 c Λ) :
    (∃ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ) ∧
      ∀ σ, NewsBundling.Unilateral.IsSPE β φ0 φ1 c 0 σ → σ.quality = β / c ∧ NewsBundling.Unilateral.eqProfit β φ1 c σ = β ^ 2 / (2 * c) := by sorry

end NewsBundling.Negotiated
