-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
-- name    : HopfAlgebra.exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/c1ffe024-dc95-56eb-be83-5c0e8d291276
-- title:
--   Ordinary normal form descends to the residue field of P
-- statement:
--   Let $p$ be a prime and let $O$ be a commutative ring equipped with ring maps $O \to \overline{\mathbb{Q}}$ (into an algebraic closure of $\mathbb{Q}$) and $O \to \mathbb{Z}/p$. Let $P \subseteq \overline{\mathbb{Q}}$ be a valuation subring such that the image of every $x \in O$ in $\overline{\mathbb{Q}}$ lies in $P$ (hypothesis `hOP`), and such that, for every $x \in O$, the image of $x$ in $\mathbb{Z}/p$ vanishes exactly when the valuation of the image of $x$ in $\overline{\mathbb{Q}}$ is $< 1$ (hypothesis `hres`). Let $A$ be a commutative ring carrying a Hopf algebra structure over $O$ whose comultiplication is cocommutative, and which is finite and free as an $O$-module. Assume that the fibre $\mathbb{Z}/p \otimes_O A$ is ordinary in the following sense: there exist commutative rings $M$ and $E$ with Hopf algebra structures over $\mathbb{Z}/p$, with $M$ finite and free over $\mathbb{Z}/p$, and a bijective bialgebra map $\Theta : \mathbb{Z}/p \otimes_O A \to M \otimes_{\mathbb{Z}/p} E$ such that $E$ is reduced and the Cartier dual [`CartierDual (ZMod p) M`](def/HopfAlgebra_CartierDual.html#L12) — the $\mathbb{Z}/p$-linear dual of $M$, with its bialgebra ring structure — is reduced. The conclusion, with $P$ made an $O$-algebra by corestricting $O \to \overline{\mathbb{Q}}$ along `hOP`, asserts the same shape over the residue field $k =$ `IsLocalRing.ResidueField P`: there exist commutative rings $M_0$, $E_0$ with Hopf algebra structures over $k$, with $M_0$ finite and free over $k$, and a bijective bialgebra map $k \otimes_P (P \otimes_O A) \to M_0 \otimes_k E_0$ such that $E_0$ is reduced and the $k$-linear dual [`CartierDual k M₀`](def/HopfAlgebra_CartierDual.html#L12) is reduced. (No finiteness or freeness is required of $E$ or of $E_0$.)
--
--   This is the base-change statement for the ordinary normal form (a multiplicative-type factor tensored with an étale factor, no local-local part) of the special fibre of a finite level of a $p$-divisible group: ordinarity over the prime field $\mathbb{F}_p$ is transported to the residue field of the valuation subring $P$ of $\overline{\mathbb{Q}}$. It is used in the Cartier-duality step [`PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced`](thm.html#PDivisibleGroup.CartierDuality.pair_eq_one_of_forall_valuation_sub_counit_lt_one_of_bijective_tensorProduct_isReduced), and its proof cites the compatibility of Cartier duals with base change, [`CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul`](thm.html#CartierDual.exists_bialgEquiv_baseChange_forall_pairing_symm_tmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bijective_tensorProduct_isReduced_cartierDual_residueField_of_zmodp_valuationSubring_of_isCocomm
    (p : ℕ) [Fact p.Prime]
    {O : Type} [CommRing O] [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    (A : Type) [CommRing A] [HopfAlgebra O A] [Coalgebra.IsCocomm O A] [Module.Finite O A] [Module.Free O A]
    (hord : ∃ (M : Type) (_ : CommRing M) (_ : HopfAlgebra (ZMod p) M) (_ : Module.Finite (ZMod p) M)
        (_ : Module.Free (ZMod p) M) (E : Type) (_ : CommRing E) (_ : HopfAlgebra (ZMod p) E)
        (Θ : ZMod p ⊗[O] A →ₐc[ZMod p] M ⊗[ZMod p] E),
        Function.Bijective Θ ∧ IsReduced E ∧ IsReduced (CartierDual (ZMod p) M)) :
    letI : Algebra O P := ((algebraMap O (AlgebraicClosure ℚ)).codRestrict P.toSubring hOP).toAlgebra
    ∃ (M₀ : Type) (_ : CommRing M₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) M₀)
        (_ : Module.Finite (IsLocalRing.ResidueField P) M₀) (_ : Module.Free (IsLocalRing.ResidueField P) M₀)
        (E₀ : Type) (_ : CommRing E₀) (_ : HopfAlgebra (IsLocalRing.ResidueField P) E₀)
        (Θ : IsLocalRing.ResidueField P ⊗[P] (P ⊗[O] A) →ₐc[IsLocalRing.ResidueField P]
          M₀ ⊗[IsLocalRing.ResidueField P] E₀),
        Function.Bijective Θ ∧ IsReduced E₀ ∧ IsReduced (CartierDual (IsLocalRing.ResidueField P) M₀) := by sorry
