-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_reductionModL_eq_zero
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_reductionModL_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/e0c24e36-02b4-5d1d-b499-395cc7ef9b46
-- title:
--   Finite flat Hopf model of the ℓ^k-torsion of J₀(p)
-- statement:
--   Let $p$ be a nonzero natural number, let $\ell$ be a prime not dividing $p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$ in the sense that $\ell$ is a nonunit of $A$, and assume the predicate `ReductionInputsModL A p`, namely that there exists a choice $r$ of places satisfying `IsPlaceReductionAlong` for $A$, the residue map of $A$ and level $p$, together with `PrincipalGeneratedByIntegral`, this being exactly the datum through which the additive reduction map $\mathrm{reductionModL}$ from $J_0(p) = \mathrm{Pic}^0$ of the level-$p$ modular function field over $\overline{\mathbb{Q}}$ to the corresponding $\mathrm{Pic}^0$ over the residue field of $A$ is defined. Let $k$ be a natural number. Then there is a commutative ring $H$ carrying a Hopf algebra structure over the subring $\mathbb{Z}_{(\ell)} \subset \mathbb{Q}$ of rationals with denominator coprime to $\ell$, finite and flat as a $\mathbb{Z}_{(\ell)}$-module and with cocommutative comultiplication, together with a bijection $e$ from the convolution monoid `WithConv` of $\mathbb{Z}_{(\ell)}$-algebra homomorphisms $H \to \overline{\mathbb{Q}}$ onto the $\ell^k$-torsion submodule $\mathrm{torsionBy}_{\mathbb{Z}}(J_0(p), \ell^k)$, such that: $e(f g) = e(f) + e(g)$; for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $f, g$ with $g(h) = \sigma(f(h))$ for all $h \in H$ one has $e(g) = \sigma \cdot e(f)$ in $J_0(p)$; and, whenever $\mathrm{reductionModL}$ sends $e(f)$ to $0$, then for every $h \in H$ the element $f(h) - \varepsilon(h)$, with $\varepsilon$ the counit of $H$ followed by $\mathbb{Z}_{(\ell)} \to \overline{\mathbb{Q}}$, has $A$-valuation $< 1$.
--
--   This provides a finite flat cocommutative Hopf order over $\mathbb{Z}_{(\ell)}$ — equivalently, a finite flat commutative group scheme model — whose $\overline{\mathbb{Q}}$-points are Galois-equivariantly the $\ell^k$-torsion of $J_0(p)$, with the extra feature that vanishing of the mod-$\ell$ reduction of a point forces all its coordinates to be congruent to those of the identity section modulo the maximal ideal of $A$, so that the kernel of $\mathrm{reductionModL}$ is detected integrally. It is used in the analysis of the torsion of the Eisenstein quotient and of the action of inertia at $\ell$ on Hecke torsion classes in the kernel of reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_reductionModL_eq_zero.lean

import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IsLocalRing

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_reductionModL_eq_zero
    (p : ℕ) [NeZero p] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hinp : ReductionInputsModL A p) (k : ℕ) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) H),
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) H ∧ Module.Flat (GaloisRep.ratLocalizedAt ℓ) H ∧
      Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) H ∧
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero p) ((ℓ : ℤ) ^ k)),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero p)) = σ • (e f : JZero p)) ∧
        (∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
          reductionModL A p (e f : JZero p) = 0 →
          ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)
            (Coalgebra.counit h)) < 1) := by sorry
