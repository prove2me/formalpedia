-- Prove2me | Theorems.Thm_MoritaEquiv_thm52_categorical
-- name    : MoritaEquiv.thm52_categorical
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T13:00:39.469333+00:00
-- url     : https://prove2.me/theorems/51475789-bd45-4284-8875-d99cb5fe9a54
-- title:
--   Separating example: the two theories are categorically equivalent
-- statement:
--   Over one sort and unary predicates $p_0,p_1,\dots$, the theories $T_1=\{\exists^{=1}x\,(x=x)\}$ and $T_2=T_1\cup\{\forall y\,(p_0(y)\to p_i(y)) : i\in\mathbb N\}$ have equivalent categories of models.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, Theorem 5.2 (first half of the proof)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 5.2 (first half): the theories `T₁ = {∃=1 x (x = x)}` and
`T₂ = T₁ ∪ {∀y (q₀ y → qᵢ y) : i ∈ ℕ}` over one sort and countably many unary predicates have
equivalent categories of models (both are discrete with `2^ℵ₀` isomorphism classes). -/
theorem thm52_categorical : CategoricallyEquivalent Thm52.T1 Thm52.T2 := by sorry

end MoritaEquiv
