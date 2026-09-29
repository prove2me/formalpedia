-- Prove2me | Theorems.Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
-- name    : HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3378b8df-2847-507e-a4d8-b870cac8427b
-- title:
--   Faithful flatness over a Hopf kernel is local on the base
-- statement:
--   Let $R$ be a commutative ring and let $H$, $H'$ be commutative Hopf algebras over $R$, and let $qc \colon H \to H'$ be a morphism of $R$-coalgebras and $R$-algebras (a `BialgHom`). Write $\operatorname{hopfKer}(qc)$ for the $R$-subalgebra of $H$ on which the two $R$-algebra maps $H \to H \otimes_R H'$ given by $h \mapsto (\mathrm{id}_H \otimes qc)(\Delta h)$ and $h \mapsto h \otimes 1$ agree, i.e. the right $H'$-coinvariants of $H$. Assume that for every maximal ideal $\mathfrak p$ of $R$ there exist a commutative ring $R_1$, an $R$-algebra structure on $R_1$ making $R_1$ flat as an $R$-module, and a local ring structure on $R_1$, such that the maximal ideal of $R_1$ lies over $\mathfrak p$ (its contraction along $R \to R_1$ is $\mathfrak p$), and such that $R_1 \otimes_R H$ is faithfully flat as a module over $\operatorname{hopfKer}(\mathrm{id}_{R_1} \otimes qc)$, the Hopf kernel of the base-changed bialgebra map $R_1 \otimes_R H \to R_1 \otimes_R H'$ over $R_1$. Then $H$ is faithfully flat as a module over $\operatorname{hopfKer}(qc)$.
--
--   This is the descent step which makes faithful flatness of a commutative Hopf algebra over the coinvariants of a bialgebra map a condition local on the base: it suffices to verify it after a flat local base change at each maximal ideal of $R$, the proof combining the compatibility of the Hopf kernel with flat base change with a local-to-global criterion for faithful flatness. It is used in the proof of [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero), where the hypothesis is supplied by a structure theorem over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.faithfullyFlat_hopfKer_of_forall_isLocalRing_faithfullyFlat_baseChange
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H')
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        Module.FaithfullyFlat
          ↥(HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
              TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H'))
          (TensorProduct R R₁ H)) :
    Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) H := by sorry
