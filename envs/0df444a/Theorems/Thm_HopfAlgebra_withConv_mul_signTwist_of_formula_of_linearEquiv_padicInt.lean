-- Prove2me | Theorems.Thm_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
-- name    : HopfAlgebra.withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/08860f0c-cc66-518d-8ed3-e037834b7943
-- title:
--   Sign twist on points is convolution-multiplicative
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $s \in \overline{\mathbb{Q}_p}$ be non-zero, and let $d_0 \in \mathbb{Z}_p$ be a unit whose image under $\mathbb{Z}_p \to \overline{\mathbb{Q}_p}$ equals $s^2$. Let $H$ be a commutative $\mathbb{Z}_p$-Hopf algebra whose comultiplication is cocommutative, and let $H'$ be a commutative $\mathbb{Z}_p$-Hopf algebra together with a $\mathbb{Z}_p$-linear isomorphism $e \colon H' \to H$. Write $P_- := \mathrm{Ring.inverse}(2) \cdot (\mathrm{id}_H - S)$, where $S$ is the antipode of $H$ and $\mathrm{Ring.inverse}(2)$ is the inverse of $2$ in $\mathbb{Z}_p$. Assume that $e$ transports the comultiplication of $H'$ into the $d_0$-twisted form: for all $a \in H'$, $(e \otimes e)(\Delta_{H'} a) = \Delta_H(e a) + (\mathrm{Ring.inverse}(d_0) - 1)\,(P_- \otimes P_-)(\Delta_H(e a))$. Let $\beta$ be a bijection from the set of $\mathbb{Z}_p$-algebra homomorphisms $H' \to \overline{\mathbb{Q}_p}$ to the set of $\mathbb{Z}_p$-algebra homomorphisms $H \to \overline{\mathbb{Q}_p}$, both carrying the convolution multiplication via `WithConv`, and assume $\beta$ is given by the formula $(\beta \varphi')(h) = \varphi'(e^{-1}(h - P_- h)) + s^{-1}\,\varphi'(e^{-1}(P_- h))$ for all $\varphi'$ and all $h \in H$. Then $\beta(f' \ast g') = \beta(f') \ast \beta(g')$ for all $f', g'$, the products being the convolution products on the two point sets.
--
--   This is the multiplicativity half of the statement that the explicit sign twist attached to a quadratic twisting datum $(s, d_0)$ identifies the $\overline{\mathbb{Q}_p}$-points of $H'$ with those of $H$ as groups under convolution; $\beta$ is here assumed given by the formula rather than constructed. It feeds [`HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt`](thm.html#HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt), where the bijection is produced and upgraded to a multiplicative equivalence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NNReal
open scoped TensorProduct in

theorem HopfAlgebra.withConv_mul_signTwist_of_formula_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (d₀ : ℤ_[p]) (hd₀s : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) d₀ = s ^ 2) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a)))
    (β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
         WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
    (hβ : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h))) :
    ∀ f' g', β (f' * g') = β f' * β g' := by sorry
