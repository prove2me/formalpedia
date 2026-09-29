-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_prolongation_pi_torsion_pic0_qExpFunctionField_of_not_dvd
-- name    : ModularCurve.exists_finiteFlat_prolongation_pi_torsion_pic0_qExpFunctionField_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b7f2f7e7-447f-5fd7-978e-e40608ce269a
-- title:
--   Finite flat pⁿ-torsion of modular Jacobians away from the level
-- statement:
--   Let $M$ be a positive natural number, let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ with $\Gamma_1(M)\le\Gamma\le\Gamma_0(M)$, let $p$ be prime with $p\nmid M$, and let $b,n$ be natural numbers. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of rationals whose denominator is coprime to $p$, and let $F$ be the subfield of $\overline{\mathbb{Q}}((q))$ obtained by adjoining to $\overline{\mathbb{Q}}$ the coefficientwise images of [`ModularCurve.qExpFunctionFieldC ℚ Γ`](def/ModularCurve_X1.html#L101), the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of integral $q$-expansions of pairs of modular forms of a common weight on $\Gamma$. The assertion is that there exist a type $G$ carrying a commutative ring structure and a Hopf algebra structure over $R$, finite and flat as an $R$-module and cocommutative as a coalgebra, together with a bijection $e$ from the $R$-algebra homomorphisms $G\to\overline{\mathbb{Q}}$, with their convolution monoid structure, onto the functions $\mathrm{Fin}\,b\to T$, where $T$ is the subgroup of elements killed by $p^n$ in the group $\mathrm{Pic}^0$ of degree-zero divisor classes of $F$ over $\overline{\mathbb{Q}}$ (finitely supported $\mathbb{Z}$-valued functions on places of $F$ of total degree zero, modulo principal divisors), such that $e(fg)=e(f)+e(g)$ for all $f,g$, and such that whenever $\sigma$ is a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ and $g=\sigma\circ f$ pointwise on $G$, then for each index $i$ the class $e(g)(i)$ equals $\sigma\cdot e(f)(i)$ in $\mathrm{Pic}^0$.
--
--   This records the good reduction at $p\nmid M$ of the Jacobian of the modular curve attached to $\Gamma$ in its model with rational cusp $\infty$: the diagonal Galois module $J(\Gamma)[p^n]^b$ is realised as the $\overline{\mathbb{Q}}$-points of a finite flat commutative group scheme over $\mathbb{Z}_{(p)}$. It feeds the flatness at $p$ of the $p$-adic representations attached to primitive forms, and the corresponding statement for diamond-twisted quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_prolongation_pi_torsion_pic0_qExpFunctionField_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_finiteFlat_prolongation_pi_torsion_pic0_qExpFunctionField_of_not_dvd
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) (b n : ℕ) :
    ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) G),
      Module.Finite (GaloisRep.ratLocalizedAt p) G ∧ Module.Flat (GaloisRep.ratLocalizedAt p) G ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) G ∧
      ∃ e : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          (Fin b → ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ)) (p ^ n))),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (G →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ x : G, g x = σ (f x)) →
            ∀ i : Fin b, ((e g i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                  (ModularCurve.qExpFunctionFieldC ℚ Γ)) (p ^ n))) :
                  AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
                    (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                      (ModularCurve.qExpFunctionFieldC ℚ Γ))) =
              σ • ((e f i : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ)
                (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                  (ModularCurve.qExpFunctionFieldC ℚ Γ)) (p ^ n))) :
                  AlgebraicCurve.Pic0 (AlgebraicClosure ℚ)
                    (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
                      (ModularCurve.qExpFunctionFieldC ℚ Γ))) := by sorry
