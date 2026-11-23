-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_coeff_integrable
-- name    : GrothendieckPD.Digits.lemma_2_5_coeff_integrable
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:52:42.831614+00:00
-- url     : https://prove2.me/theorems/1a292433-ab0a-42c1-98a5-14c62d12897d
-- title:
--   Lemma 2.5: measurability and integrability of mixed Hermite coefficients
-- statement:
--   If $(F,G)$ is the jointly measurable random pair of a mixed rounding scheme, then for every fixed degree $m$ the random coefficient
--   $$\omega\longmapsto c_m(F_\omega,G_\omega)$$
--   is integrable with respect to the scheme's probability measure. This is the measurability/integrability step implicit when the proof of Lemma 2.5 averages $\mathbb E\sum_m|c_m(f,g)|\le1$ and interchanges expectation with the coefficient integrals.
--
--   **Formalization Note** The statement uses exactly the published `GrothendieckLB.MixedScheme` random-pair representation and the finite moment-sum definition `coeff`; no oddness hypothesis is needed.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.5 proof, p. 5 (averaging the pair coefficient estimates)

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
open MeasureTheory Filter

namespace GrothendieckPD.Digits

/-- For each degree, the pair coefficient is integrable over a mixed scheme. -/
theorem lemma_2_5_coeff_integrable :
    ∀ (n m : ℕ) (S : GrothendieckLB.MixedScheme n),
      MeasureTheory.Integrable (fun ω => coeff m (S.F ω) (S.G ω)) S.μ := by sorry
