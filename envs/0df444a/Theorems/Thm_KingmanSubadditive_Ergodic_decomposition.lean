-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_decomposition
-- name    : KingmanSubadditive.Ergodic.decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:42:34.037708+00:00
-- url     : https://prove2.me/theorems/6105a419-c747-4981-8e0b-5ac74d1b3a6d
-- title:
--   (1.2.6): additive plus nonnegative subadditive decomposition
-- statement:
--   Every subadditive process $x$ admits, on the same probability space, a decomposition $x_{st}=y_{st}+z_{st}$ for every $s<t$, almost surely, where $y$ is an additive process, $z$ is a nonnegative subadditive process, and
--   $$E_P(y_{01})=\gamma(x),\qquad \gamma(z)=0.$$
--   This is the decomposition Kingman names as the basis of the earlier proof of Theorem 1. Each component retains the process assumptions, including joint stationarity.
--
--   **Formalization Note** Equality and nonnegativity are asserted almost surely for each index pair. The index set is countable, so they hold simultaneously off a single null set.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, (1.2.6) and following sentence

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 885, (1.2.6) and the following sentence, quoted from [8]. The two
components live on the same probability space as `x`. Equalities and
nonnegativity of random variables are stated almost surely at each valid
index pair. -/
theorem decomposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    ∃ y z : ℕ → ℕ → Ω → ℝ,
      IsAdditiveProcess P y ∧
      mean P y 1 = gamma P x ∧
      IsSubadditiveProcess P z ∧
      (∀ (s t : ℕ), s < t → ∀ᵐ ω ∂P, 0 ≤ z s t ω) ∧
      gamma P z = 0 ∧
      (∀ (s t : ℕ), s < t → ∀ᵐ ω ∂P,
        x s t ω = y s t ω + z s t ω) := by sorry

end KingmanSubadditive.Ergodic
