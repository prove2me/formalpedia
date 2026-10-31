-- Prove2me | Theorems.Thm_KallMayerSLP_RiskMeasures_proposition_7_1
-- name    : KallMayerSLP.RiskMeasures.proposition_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:40:59.275653+00:00
-- url     : https://prove2.me/theorems/e0cda5c5-65a0-48c6-8635-e696216770f2
-- title:
--   Proposition 7.1 — positive homogeneity with subadditivity is equivalent to positive homogeneity with convexity
-- statement:
--   Let $g:X\to\mathbb R$ be a function on a real linear space $X$. Then:
--
--   1. if $g$ is positive homogeneous and subadditive, then $g$ is convex;
--   2. if $g$ is positive homogeneous and convex, then $g$ is subadditive.
--
--   Here positive homogeneity means $g(\lambda x)=\lambda g(x)$ for all $\lambda\ge0$, $x\in X$, and subadditivity $g(x+y)\le g(x)+g(y)$ for all $x,y\in X$. The proposition is the bridge between the axiom systems (7.2) and (7.3): a convex risk measure is coherent exactly when it is positively homogeneous.
--
--   Differences from the source: none.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7, Proposition 7.1, p.181 (PDF 191)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Proposition 7.1** (sublinear functions).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7, Prop. 7.1, p.181 (PDF 191). Let `g : X → ℝ` be a function on a linear space `X`. Then
a) if `g` is both positive homogeneous and subadditive then it is convex;
b) if `g` is positive homogeneous and convex, then it is subadditive.

**Formalization Note.** `X` is any real vector space; convexity is `ConvexOn ℝ univ g`. -/
theorem proposition_7_1 {X : Type*} [AddCommGroup X] [Module ℝ X] (g : X → ℝ) :
    (IsPosHomogeneous g → IsSubadditive g → ConvexOn ℝ Set.univ g) ∧
    (IsPosHomogeneous g → ConvexOn ℝ Set.univ g → IsSubadditive g) := by sorry

end KallMayerSLP.RiskMeasures
