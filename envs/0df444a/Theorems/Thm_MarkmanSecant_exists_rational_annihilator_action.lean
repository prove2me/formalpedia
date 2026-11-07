-- Prove2me | Theorems.Thm_MarkmanSecant_exists_rational_annihilator_action
-- name    : MarkmanSecant.exists_rational_annihilator_action
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T04:25:51.847453+00:00
-- url     : https://prove2.me/theorems/35106298-0f52-4c32-b19f-c4b5b88831e5
-- title:
--   Rational descent of the opposite scalar action on a quadratic secant
-- statement:
--   Let $d>0$ be rational, let $a,b$ be rational classes in the even spin representation, and suppose $s_+=a+\sqrt{-d}\,b$ and $s_-=a-\sqrt{-d}\,b$ are even pure spinors with disjoint annihilators. Construct a rational matrix $F$ whose complex-linear extension acts by $\sqrt{-d}$ on $\operatorname{ann}(s_+)$ and by $-\sqrt{-d}$ on $\operatorname{ann}(s_-)$. This isolates the rational-descent step in the secant construction. Once this action is available, its square and its pairing-scaling factor follow from the complementary, isotropic annihilator decomposition. No square or pairing identity is assumed in this statement.
-- source:
--   Markman, Cycles on abelian 2n-folds of Weil type from secant sheaves on abelian n-folds, arXiv:2502.03415v2, Section 2.2, the rational descent immediately preceding equation (2.2.4), with lambda = sqrt(-d). https://arxiv.org/html/2502.03415v2

import Mathlib
import Definitions.Def_MarkmanSecant

open MarkmanSecant
open scoped ExteriorAlgebra

namespace MarkmanSecant

theorem exists_rational_annihilator_action (n : ℕ) (d : ℚ) (hd : 0 < d) (a b : Spinor n)
    (ha : IsRationalClass a) (hb : IsRationalClass b)
    (h₁ : IsEvenPureSpinor (a + sqrtNeg d • b)) (h₂ : IsEvenPureSpinor (a - sqrtNeg d • b))
    (h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥) :
    ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
      (∀ v ∈ annih (a + sqrtNeg d • b), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
      (∀ v ∈ annih (a - sqrtNeg d • b), (ratMatV F).mulVec v = (-sqrtNeg d) • v) := by sorry

end MarkmanSecant
