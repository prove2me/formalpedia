-- Prove2me | Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one
-- name    : GaloisRep.mem_ratLocalizedAt_iff_padic_norm_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/1a2bf5ae-36e4-5033-bbdf-e0189da7e385
-- title:
--   ℤ₍ₚ₎ = ℚ ∩ ℤₚ via p-adic norm
-- statement:
--   Let $p$ be a prime and let $q$ be a rational number. The subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ is by definition the set of rationals whose denominator (the positive denominator of the reduced fraction) is coprime to $p$; closure under multiplication, addition and negation, and membership of $0$ and $1$, are part of that definition. The theorem asserts the equivalence: $q$ lies in [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) if and only if the $p$-adic norm of the image of $q$ under the canonical embedding $\mathbb{Q} \hookrightarrow \mathbb{Q}_{[p]}$ satisfies $\lVert q \rVert \le 1$. In other words, the localisation $\mathbb{Z}_{(p)}$, realised here as the subring of rationals with denominator prime to $p$, is exactly the intersection of $\mathbb{Q}$ with the valuation ring $\mathbb{Z}_p$ inside $\mathbb{Q}_p$.
--
--   This is the standard identification $\mathbb{Z}_{(p)} = \mathbb{Q} \cap \mathbb{Z}_p$, giving an archimedean-free criterion for $p$-integrality of a rational number. It is used to pass between denominator conditions and $p$-adic norm bounds, in particular in [`HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match`](thm.html#HopfAlgebra.basis_structureConstants_mem_ratLocalizedAt_range_of_bialgHom_basis_match), where structure constants bounded $p$-adically are recognised as $p$-integral rationals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_mem_ratLocalizedAt_iff_padic_norm_le_one.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.mem_ratLocalizedAt_iff_padic_norm_le_one
    (p : ℕ) [Fact p.Prime] (q : ℚ) :
    q ∈ GaloisRep.ratLocalizedAt p ↔ ‖(q : ℚ_[p])‖ ≤ 1 := by sorry
