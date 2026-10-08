-- Prove2me | Theorems.Thm_FournierGuillin_Conc_lemma_11
-- name    : FournierGuillin.Conc.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:01.312978+00:00
-- url     : https://prove2.me/theorems/ef92133b-5bb6-4ac7-9c60-8b66c1f0f988
-- title:
--   Lemma 11, p. 12 — ℙ[X = N + k] ≥ κ₀N^{−1/2}, κ₀ = e^{−2}/√2, for X ~ Poisson(N), 0 ≤ k ≤ ⌊√N⌋
-- statement:
--   For every integer $N\ge1$, if $X$ is Poisson($N$)-distributed, then for every $k\in\{0,\dots,\lfloor\sqrt N\rfloor\}$,
--   $$\mathbb P[X=N+k]\ge\kappa_0N^{-1/2},\qquad\kappa_0=\frac{e^{-2}}{\sqrt2}.$$
--
--   This local lower bound on the Poisson distribution near its mean is what allows passing from the Poissonized sample size back to a deterministic one (depoissonization) in Proposition 10.
--
--   **Formalization Note** $\lfloor\sqrt N\rfloor$ is `Nat.sqrt N`, and the law of $X$ is Mathlib's `poissonMeasure N`.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Lemma 11, p. 12; proof p. 13

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Lemma 11 (p. 12): for all `N ≥ 1`, `X` Poisson(`N`)-distributed and `k ∈ {0, …, ⌊√N⌋}`,
`ℙ[X = N + k] ≥ κ₀ N^{-1/2}` with `κ₀ = e^{-2}/√2`. -/
theorem lemma_11 (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ Nat.sqrt N) :
    ENNReal.ofReal (Real.exp (-2) / Real.sqrt 2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≤
      ProbabilityTheory.poissonMeasure (N : ℝ≥0) {N + k} := by sorry

end FournierGuillin.Conc
