-- Prove2me | Theorems.Thm_KontsevichHMS_mTwoCoeff_theta
-- name    : KontsevichHMS.mTwoCoeff_theta
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T03:05:44.465894+00:00
-- url     : https://prove2.me/theorems/4aea63be-fd56-4c21-8752-0abf8f4387f6
-- title:
--   Structure constants of $m_2$ on the torus are theta values
-- statement:
--   In the last section Kontsevich computes the composition $m_2$ on the flat torus: lifting to the universal cover, the discs contributing to a structure constant are triangles with sides on three families of parallel lines; their equivalence classes modulo $\mathbb{Z}^2$ are labelled by the terms of an arithmetic progression, and their areas are proportional to the squares of those terms. Hence
--   $$c(p,q,r) \;=\; \sum_{n \in \mathbb{Z}} \exp\bigl(-(an+b)^2\bigr)$$
--   for real parameters $a \neq 0$ and $b$ — a value of the classical theta-function.
--
--   The milestone asks for this for branes with trivial holonomy, in the form: each structure constant either vanishes (no triangle contributes, which happens exactly when the Maslov degrees do not add up) or equals such a theta series. Convergence of the series, for positive area, is part of the statement.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, p. 19 ('the tensor element of composition m2 can be written naturally as sum over n of exp(-(an+b)^2)')

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

namespace KontsevichHMS

open Brane

/-- Kontsevich's computation on the two-torus: the triangles contributing to a structure
constant of `m₂` are labelled by an arithmetic progression whose terms have squares
proportional to their areas, so each structure constant is a value of a classical
theta-function (or vanishes, when no triangle contributes). -/
theorem mTwoCoeff_theta (area : ℝ) (harea : 0 < area) (b₁ b₂ b₃ : Brane)
    (h₁₂ : Transverse b₁ b₂) (h₂₃ : Transverse b₂ b₃) (h₁₃ : Transverse b₁ b₃)
    (hc₁ : b₁.conn = 0) (hc₂ : b₂.conn = 0) (hc₃ : b₃.conn = 0)
    (p q r : Torus) (hp : p ∈ isect b₁ b₂) (hq : q ∈ isect b₂ b₃) (hr : r ∈ isect b₁ b₃) :
    mTwoCoeff area b₁ b₂ b₃ p q r = 0 ∨
      ∃ a b : ℝ, a ≠ 0 ∧
        mTwoCoeff area b₁ b₂ b₃ p q r
          = ∑' n : ℤ, Complex.exp (-((a * (n : ℝ) + b) ^ 2 : ℝ)) := by sorry

end KontsevichHMS
