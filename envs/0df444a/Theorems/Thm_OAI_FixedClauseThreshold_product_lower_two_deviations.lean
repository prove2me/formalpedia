-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_product_lower_two_deviations
-- name    : OAI.FixedClauseThreshold.product_lower_two_deviations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:10:38.029086+00:00
-- url     : https://prove2.me/theorems/deec509c-3308-4c8e-a70b-db91eecfd494
-- title:
--   Product lower bound $\kappa^2(1-x-y)\le ab$ from two deviation thresholds
-- statement:
--   Let $\kappa,x,y,a,b$ be real numbers with $\kappa\ge 0$, $x\ge 0$, $y\ge 0$, $a\ge 0$ and $b\ge 0$. Suppose that $\kappa\le a$ whenever $x<1$, and that $\kappa\le b$ whenever $y<1$. Then
--
--   $$
--   \kappa^2\,(1-x-y)\le ab.
--   $$
--
--   This elementary inequality is a pointwise Chebyshev-type device. In its application, $x$ and $y$ are the squared deviation of a binomial count normalized by two different windows, while $a$ and $b$ are probabilities known to be at least $\kappa$ as long as the deviation stays inside the corresponding window. Averaging the inequality over the binomial distribution then turns a second-moment bound into a lower bound for the mean of the product $ab$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Transfer.lean#L373-L390

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.product_lower_two_deviations {κ x y a b : ℝ} (hκ : 0 ≤ κ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hax : x < 1 → κ ≤ a) (hby : y < 1 → κ ≤ b) :
    κ^2 * (1 - x - y) ≤ a * b := by sorry
