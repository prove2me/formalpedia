-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_card_le_volume_ratio
-- name    : OAI.SubsphereRegression.card_le_volume_ratio
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:04:03.527139+00:00
-- url     : https://prove2.me/theorems/d6d5fa73-abb3-4df3-b0da-26c7b91c4b2c
-- title:
--   Volumetric bound on the size of a separated set in a ball
-- statement:
--   Let $E$ be a finite-dimensional real normed space of dimension $d=\dim E$, with its Borel $\sigma$-algebra. Let $s\subseteq E$ be a finite set and let $r>0$ and $R\ge0$ be real numbers such that every point of $s$ has norm at most $R$ and any two distinct points of $s$ are at distance at least $r$:
--   $$\|x\|\le R\quad(x\in s),\qquad\|x-y\|\ge r\quad(x,y\in s,\ x\ne y).$$
--   Then
--   $$|s|\le\left(\frac{R+r/2}{r/2}\right)^{d}.$$
--
--   This is the classical volumetric packing bound: an $r$-separated set in a ball of radius $R$ has at most $(1+2R/r)^{d}$ points. With $R=1$ and $r\le1$ it gives the bound $(3/r)^{d}$ used to build small nets of the unit ball, and its explicit dependence on the dimension makes the covering estimates for tubes around affine subspaces quantitative.
--
--   **Formalization Note** The dimension is `Module.finrank ℝ E` and distances are `dist x y = ‖x - y‖`. The Borel $\sigma$-algebra is only used through the additive Haar measure in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Geometry.lean#L132-L173

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.card_le_volume_ratio (s : Finset E) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hs : ∀ x ∈ s, ‖x‖ ≤ R)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ dist x y) :
    (s.card : ℝ) ≤ ((R + r / 2) / (r / 2)) ^ Module.finrank ℝ E := by sorry
