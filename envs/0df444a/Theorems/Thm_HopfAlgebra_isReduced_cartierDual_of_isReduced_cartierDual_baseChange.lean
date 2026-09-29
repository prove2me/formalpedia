-- Prove2me | Theorems.Thm_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange
-- name    : HopfAlgebra.isReduced_cartierDual_of_isReduced_cartierDual_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/2278c688-420d-5299-851c-d2e4f9331cde
-- title:
--   Reducedness of the Cartier dual descends along field extensions
-- statement:
--   Let $K$ be a field and $A$ a commutative ring carrying a Hopf algebra structure over $K$ whose comultiplication is cocommutative, and which is finite and free as a $K$-module. Let $L$ be a field equipped with a $K$-algebra structure. Here [`CartierDual K A`](def/HopfAlgebra_CartierDual.html#L12) is by definition the $K$-linear dual $\mathrm{Hom}_K(A,K)$ of $A$, equipped with the ring structure transported from the Hopf structure of $A$, i.e. with convolution product $(\chi\psi)(a)=\sum \chi(a_{(1)})\psi(a_{(2)})$ coming from the comultiplication and with unit the counit of $A$; likewise [`CartierDual L (L \otimes_K A)`](def/HopfAlgebra_CartierDual.html#L12) is the $L$-linear dual of the base change $L\otimes_K A$ with its induced Hopf structure over $L$. The hypothesis is that the ring [`CartierDual L (L ⊗[K] A)`](def/HopfAlgebra_CartierDual.html#L12) is reduced. The conclusion is that the ring [`CartierDual K A`](def/HopfAlgebra_CartierDual.html#L12) is reduced, that is, it has no nonzero nilpotent elements.
--
--   This is the statement that multiplicative type (reducedness of the Cartier dual, equivalently diagonalisability of the dual finite group scheme) may be tested after an extension of the base field. It is used in the analysis of the torus quotient of the Néron object attached to a modular curve at $p$, via the statements [`HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing`](thm.html#HopfAlgebra.exists_verschiebung_bialgEquiv_and_sub_counit_mem_and_finrank_of_baseChange_bialgEquiv_addMonoidAlgebra_and_isLocalRing) and [`ModularCurve.exists_verschiebung_bialgEquiv_torusQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness`](thm.html#ModularCurve.exists_verschiebung_bialgEquiv_torusQuotient_finPts_jHNeronObjectAtP_of_finPtsWitness).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isReduced_cartierDual_of_isReduced_cartierDual_baseChange.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.isReduced_cartierDual_of_isReduced_cartierDual_baseChange
    (K : Type) [Field K] (A : Type) [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A]
    [Module.Finite K A] [Module.Free K A]
    (L : Type) [Field L] [Algebra K L]
    (hL : IsReduced (CartierDual L (L ⊗[K] A))) :
    IsReduced (CartierDual K A) := by sorry
