-- Prove2me | Theorems.Thm_IsAdicComplete_exists_isPrimitiveRoot_of_residueField
-- name    : IsAdicComplete.exists_isPrimitiveRoot_of_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/f4e85460-f1b9-5011-bf48-ca555f40f1af
-- title:
--   Primitive n-th roots of unity lift along the residue map
-- statement:
--   Let $W$ be a commutative local ring which is adically complete with respect to its maximal ideal $\mathfrak m_W$, and let $n$ be a natural number with $n > 0$ whose image $n \cdot 1$ in $W$ is a unit. Assume that the residue field $W/\mathfrak m_W$ contains an element $\zeta_0$ that is a primitive $n$-th root of unity in Mathlib's sense, that is, $\zeta_0^n = 1$ and every $l$ with $\zeta_0^l = 1$ satisfies $n \mid l$. The conclusion is that $W$ itself contains an element $\zeta$ which is a primitive $n$-th root of unity in the same sense: $\zeta^n = 1$, and $\zeta^l = 1$ implies $n \mid l$ for all natural numbers $l$. Nothing is assumed about $W$ beyond commutativity, locality and adic completeness; in particular $W$ is not required to be Noetherian, a domain, or of any particular residue characteristic, and no uniqueness or compatibility of the lift $\zeta$ beyond its existence is asserted (although the lift produced does reduce to $\zeta_0$).
--
--   This is the Hensel-lifting statement that the group of $n$-th roots of unity of a complete local ring surjects onto that of its residue field when $n$ is invertible, the Teichmüller-type lifting used to manufacture roots of unity inside coefficient rings. It is invoked when constructing étale local extensions with prescribed residue data and in the analysis of the local models of the modular curve $X_1$ at supersingular points over rings containing $\zeta_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAdicComplete_exists_isPrimitiveRoot_of_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem IsAdicComplete.exists_isPrimitiveRoot_of_residueField
    {W : Type*} [CommRing W] [IsLocalRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (n : ℕ) (hn : 0 < n) (hnW : IsUnit (n : W))
    (hk : ∃ ζ₀ : IsLocalRing.ResidueField W, IsPrimitiveRoot ζ₀ n) :
    ∃ ζ : W, IsPrimitiveRoot ζ n := by sorry
