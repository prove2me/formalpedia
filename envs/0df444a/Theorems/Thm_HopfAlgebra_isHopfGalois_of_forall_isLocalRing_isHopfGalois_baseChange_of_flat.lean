-- Prove2me | Theorems.Thm_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
-- name    : HopfAlgebra.isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/377b5057-52df-5f76-8ccc-232a29e0b5b5
-- title:
--   Hopf–Galois property is local on the base along flat local covers
-- statement:
--   Let $R$ be a commutative ring, let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ and flat as an $R$-module, let $H'$ be a commutative ring carrying a Hopf algebra structure over $R$, and let $qc \colon H \to H'$ be a morphism of $R$-bialgebras that is surjective as a map of sets. Assume that for every maximal ideal $\mathfrak p$ of $R$ there is a commutative ring $R_1$, equipped with an $R$-algebra structure making it flat over $R$, which is a local ring whose maximal ideal lies over $\mathfrak p$, and such that the base-changed bialgebra map $\mathrm{id}_{R_1} \otimes qc \colon R_1 \otimes_R H \to R_1 \otimes_R H'$ over $R_1$ has the property `IsHopfGalois`. Then $qc$ itself has the property `IsHopfGalois`, that is: the canonical $R$-linear map $H \otimes_R H \to H \otimes_R H'$ underlying the canonical algebra map attached to $qc$ is surjective, and every element $z$ of $H \otimes_R H$ killed by it lies in the $R$-submodule spanned by the balancing relations $(a h) \otimes a' - a \otimes (h a')$ with $a, a' \in H$ and $h$ in the Hopf kernel of $qc$. No faithful flatness of $R_1$ over $R$ is required in the hypothesis, only flatness together with the condition that the maximal ideal of $R_1$ lies over $\mathfrak p$.
--
--   This is the local-global principle for the Hopf–Galois (quotient-torsor) property of a surjective bialgebra quotient: it suffices to verify the property after a flat local base change at each maximal ideal of the base. It is used in the proof of the characteristic-zero statement [`HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero`](thm.html#HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective_of_moduleFinite_baseChange_of_charZero), where the local models come from the structure theory over local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.isHopfGalois_of_forall_isLocalRing_isHopfGalois_baseChange_of_flat
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Flat R H]
    (H' : Type) [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') (hqc : Function.Surjective qc)
    (hloc : ∀ (p : Ideal R), p.IsMaximal →
      ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁) (_ : IsLocalRing R₁),
        (IsLocalRing.maximalIdeal R₁).LiesOver p ∧
        HopfAlgebra.IsHopfGalois (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
            TensorProduct R R₁ H →ₐc[R₁] TensorProduct R R₁ H')) :
    HopfAlgebra.IsHopfGalois qc := by sorry
