-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_eventually_log_pow_le
-- name    : OAI.ShortEgyptian.eventually_log_pow_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:52:46.368906+00:00
-- url     : https://prove2.me/theorems/60ed638c-e9af-4ca9-a01e-802645248b1e
-- title:
--   Polynomials in $\log S$ are eventually dominated by $S^{\varepsilon}$
-- statement:
--   Let $C$ be a real number, $k$ a natural number and $\varepsilon>0$. Then for all sufficiently large real $S$,
--
--   $$
--   C\,(1+\log S)^k\le S^{\varepsilon}.
--   $$
--
--   That is, there is $S_0$ such that the inequality holds for every $S\ge S_0$.
--
--   This is the standard fact that every power of the logarithm grows more slowly than every positive power, in a form with the shift $1+\log S$ and an arbitrary (possibly negative) constant $C$. It is used to check the numerical hypotheses of explicit estimates, such as $40(1+\log S)\le S^{1/16}$, for all large $S$.
--
--   **Formalization Note** "For all sufficiently large $S$" is the filter statement `∀ᶠ S : ℝ in atTop`, and $S^{\varepsilon}$ is the real power `S ^ eps`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean#L12-L27

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
open Filter Topology Asymptotics

theorem OAI.ShortEgyptian.eventually_log_pow_le (C : ℝ) (k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ S : ℝ in atTop, C * (1+Real.log S)^k ≤ S^eps := by sorry
