-- Prove2me | Theorems.Thm_InfFisher_EG_lemma_A_1
-- name    : InfFisher.EG.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:18:17.169984+00:00
-- url     : https://prove2.me/theorems/ccc7e323-be92-4842-8947-4a13e21b3341
-- title:
--   Lemma A.1, p. a1 — convex compact utility range and purification
-- statement:
--   Let $\mu_1,\ldots,\mu_m$ be finite measures on a common measurable space. A fractional partition consists of nonnegative measurable weights $x_1,\ldots,x_p$ summing to one; a pure partition consists of measurable, disjoint sets $\Theta_1,\ldots,\Theta_p$ covering the space. Let $\mathcal U$ and $\mathcal U'$ be their respective matrices of measured shares. Then
--
--   $$\mathcal U\text{ is convex and compact},\qquad
--     (\forall i,\ \mu_i\text{ atomless})\Longrightarrow\mathcal U'=\mathcal U.$$
--
--   This range result supplies the purification step used in the market's feasible utility set.
--
--   **Formalization Note** Fractional weights sum to one everywhere. Atomlessness is divisibility of every measurable set, as defined on p. 6 of the paper.
-- source:
--   Gao & Kroer, Infinite-Dimensional Fisher Markets and Tractable Fair Division, arXiv:2010.03025v5, Lemma A.1, p. a1 (PDF 36)

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_EG_Setting

namespace InfFisher.EG

open MeasureTheory

theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] {m p : ℕ}
    (μs : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μs i)] :
    Convex ℝ (dwwU μs p) ∧ IsCompact (dwwU μs p) ∧
      ((∀ i, IsAtomless (μs i)) → dwwU' μs p = dwwU μs p) := by sorry

end InfFisher.EG
