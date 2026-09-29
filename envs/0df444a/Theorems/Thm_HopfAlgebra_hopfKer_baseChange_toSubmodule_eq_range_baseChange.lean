-- Prove2me | Theorems.Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange
-- name    : HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3657e65a-8f20-500c-9d45-896a2eabd85f
-- title:
--   Hopf kernels commute with flat base change
-- statement:
--   Let $R$ be a commutative ring and $R_1$ a commutative $R$-algebra that is flat as an $R$-module, and let $H$ and $H'$ be commutative Hopf algebras over $R$, with $qc \colon H \to H'$ a morphism of $R$-bialgebras. For a bialgebra morphism $\pi \colon A \to B$ the predicate [`HopfAlgebra.hopfKer`](def/HopfAlgebra_HopfKer.html#L19) denotes the subalgebra of $A$ on which the coaction $(\mathrm{id}_A \otimes \pi) \circ \Delta_A \colon A \to A \otimes B$ agrees with $a \mapsto a \otimes 1$, i.e. the equaliser of these two algebra maps. Form the base-changed bialgebra morphism $\mathrm{id}_{R_1} \otimes qc \colon R_1 \otimes_R H \to R_1 \otimes_R H'$, a morphism of $R_1$-bialgebras. The assertion is an equality of $R_1$-submodules of $R_1 \otimes_R H$: the submodule underlying the Hopf kernel of $\mathrm{id}_{R_1} \otimes qc$ coincides with the range of the $R_1$-linear base change along $R_1$ of the inclusion $\mathrm{hopfKer}(qc) \hookrightarrow H$, i.e. with the image of $R_1 \otimes_R \mathrm{hopfKer}(qc)$ in $R_1 \otimes_R H$. Here $R$ and $R_1$ lie in the same universe, while $H$ and $H'$ are arbitrary.
--
--   This is the statement that formation of Hopf kernels (coinvariants for the coaction induced by a bialgebra quotient) commutes with flat base change, recorded as an equality of submodules rather than of subalgebras. It is used in the study of Hopf kernels under passage to flat, local or fraction-field extensions of the base, and is cited by results on faithful flatness of Hopf kernels and of quotients by idempotent-generated ideals, and on restriction of points over algebraically closed fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v w

theorem HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange
    {R : Type u} [CommRing R] (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Module.Flat R R₁]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') :
    Subalgebra.toSubmodule
        (HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
          R₁ ⊗[R] H →ₐc[R₁] R₁ ⊗[R] H'))
      = LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange R₁) := by sorry
