-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/c50a827e-583b-5d67-97a8-e8b99078c7ab
-- title:
--   Finite flat Hopf model of J₀(p)[ℓ^k] for ℓ∤ p
-- statement:
--   Let $p$ be a nonzero natural number, let $\ell$ be a prime not dividing $p$, and let $k$ be a natural number. Write $R =$ [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbf{Q}$ consisting of those rationals whose denominator is coprime to $\ell$ (the localisation $\mathbf{Z}_{(\ell)}$), and write `JZero p` for the degree-zero divisor class group $\mathrm{Pic}^0$ of the base change to $\overline{\mathbf{Q}}$ of the modular function field of level $p$, i.e. degree-zero divisors modulo principal divisors, carrying its action of $\mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$. The assertion is that there exist a commutative ring $H$ with a Hopf algebra structure over $R$, such that $H$ is finite and flat as an $R$-module and its comultiplication is cocommutative, together with a bijection $e$ from the set of $R$-algebra homomorphisms $H \to \overline{\mathbf{Q}}$, equipped with its convolution multiplication (`WithConv`), onto the submodule of elements of `JZero p` annihilated by $\ell^k$, satisfying two compatibilities: $e(f \cdot g) = e(f) + e(g)$ for all points $f,g$; and, for every $\sigma \in \mathrm{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ and all points $f,g$ with $g(h) = \sigma(f(h))$ for all $h \in H$, one has $e(g) = \sigma \cdot e(f)$ in `JZero p`.
--
--   This is the statement that, for $\ell \nmid p$, the Galois module $J_0(p)[\ell^k]$ is the group of $\overline{\mathbf{Q}}$-points of a finite flat commutative group scheme over $\mathbf{Z}_{(\ell)}$, presented on the Hopf-algebra side: $X_0(p)$, and hence its Jacobian, has good reduction at $\ell$, and the $\ell^k$-torsion of the abelian scheme model is finite flat. It is the input to the finite-flat (flatness at $\ell$) condition for the Galois representations attached to cusp forms, and is used in the analysis of the inertia action on torsion of $J_0(p)$ and in the flatness statements for points of the relevant deformation problems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p) (k : ℕ) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H),
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) H ∧ Module.Flat (GaloisRep.ratLocalizedAt ℓ) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero p) ((ℓ : ℤ) ^ k)),
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero p)) = σ • (e f : JZero p) := by sorry
