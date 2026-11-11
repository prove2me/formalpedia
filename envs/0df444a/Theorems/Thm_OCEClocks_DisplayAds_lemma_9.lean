-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_9
-- name    : OCEClocks.DisplayAds.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:22:10.623187+00:00
-- url     : https://prove2.me/theorems/979901b5-00e8-4a4d-98fb-d324d4796885
-- title:
--   Lemma 9 — the First-Age Poisson generator is an OCEC generator
-- statement:
--   Let $\lambda>0$. The First-Age Poisson generator with arrival rate $\lambda$ is an OCEC generator (Definition 2). For every number $n$ of requests and every input sequence $x\in[0,1]^n$ fixed independently of its randomness:
--
--   1. each returned clock satisfies $Y_j\sim\mathrm{Exp}(x_j)$, with $\mathrm{Exp}(0)$ the point mass at $\infty$;
--   2. the clocks $(Y_j)_{j}$ are negatively associated.
--
--   In addition, $Y_j$ depends on the input only through $x_1,\dots,x_j$.
--
--   This makes the generator usable in OCEC rounding, so Lemma 6 applies to it in the Display Ads algorithm.
--
--   **Formalization Note** `IsOCECGenerator (generatorLaw λ n) (firstAgeGenerator λ n)` for every `n`. The randomness is one stationary Poisson process and $n$ independent uniforms.
--
--   Differences from the source:
--   - encoding: finite sets I (resources) and J (requests), J indexed in arrival order → Fin m and Fin n, with the order of Fin n as the arrival order; reason: every finite ordered set is in bijection with some Fin
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 9, Lemma 9

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_OCEC
import Definitions.Def_OCEClocks_DisplayAds_FirstAgeGenerator

namespace OCEClocks.DisplayAds

/-- Lemma 9 (p. 9): the First-Age Poisson generator (rate `λ > 0`) is an OCEC generator, for every
number `n` of requests. -/
theorem lemma_9 (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    IsOCECGenerator (generatorLaw lam n) (firstAgeGenerator lam n) := by sorry

end OCEClocks.DisplayAds
