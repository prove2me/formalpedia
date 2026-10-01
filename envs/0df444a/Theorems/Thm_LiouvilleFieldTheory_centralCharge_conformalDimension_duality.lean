-- Prove2me | Theorems.Thm_LiouvilleFieldTheory_centralCharge_conformalDimension_duality
-- name    : LiouvilleFieldTheory.centralCharge_conformalDimension_duality
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-01T09:51:57.871111+00:00
-- url     : https://prove2.me/theorems/707e9191-97ff-4831-9c62-33ab1e1b0235
-- title:
--   Duality $b \to 1/b$ preserves $c$ and $\Delta$
-- statement:
--   Let $c(b) = 1 + 6(b + 1/b)^2$ and $\Delta_b(\alpha) = \alpha(b + 1/b - \alpha)$. For every $b \in \mathbb{C}$ and every momentum $\alpha \in \mathbb{C}$,
--   $$c(1/b) = c(b) \qquad\text{and}\qquad \Delta_{1/b}(\alpha) = \Delta_b(\alpha).$$
--
--   The central charge and the conformal dimensions are invariant under the duality $b \to 1/b$; correlation functions are covariant under it, although the exponential potential of the Lagrangian is not invariant.
--
--   **Formalization Note** $1/b$ is Lean's inverse $b^{-1}$, with $0^{-1} = 0$, so $b = 0$ is a trivial case.
-- source:
--   Wikipedia, "Liouville field theory", revision oldid=1376996606 (https://en.wikipedia.org/w/index.php?title=Liouville_field_theory&oldid=1376996606); section Introduction (p. 2): "The central charge and conformal dimensions are invariant under the duality b → 1/b".

import Mathlib
import Definitions.Def_LiouvilleFieldTheory_kinematics
open Complex

namespace LiouvilleFieldTheory

theorem centralCharge_conformalDimension_duality (b α : ℂ) :
    centralCharge b⁻¹ = centralCharge b ∧
      conformalDimension b⁻¹ α = conformalDimension b α := by
  sorry

end LiouvilleFieldTheory
