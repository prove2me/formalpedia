-- Prove2me | Theorems.Thm_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
-- name    : IsLocalRing.exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/da04f623-ec1b-5327-8bc0-1b6d14a53f3b
-- title:
--   Power series ring from smoothness and one-dimensional tangent space
-- statement:
--   Let $\Lambda$ be a Noetherian local ring that is complete (adically complete for its maximal ideal), and let $R$ be a Noetherian local $\Lambda$-algebra, likewise complete for its maximal ideal, such that the composite $\Lambda \to R \to k$ with the residue map of $R$ is surjective, where $k =$ `ResidueField R`; the ring of dual numbers $k[\varepsilon]$, $\varepsilon^2 = 0$, carries its $\Lambda$-algebra structure. Assume: (i) a smoothness condition — for all local Artinian $\Lambda$-algebras $A$, $B$ in the universe of $\Lambda$ whose residue maps composed with the structure maps from $\Lambda$ are surjective, every surjective $\Lambda$-algebra map $\pi : B \to A$ whose kernel is annihilated by the maximal ideal of $B$, and every $\Lambda$-algebra map $g : R \to A$, there is a $\Lambda$-algebra map $g' : R \to B$ with $g'$ followed by $\pi$ equal to $g$; (ii) a $\Lambda$-algebra map $\Phi_1 : R \to k[\varepsilon]$ whose constant component is the residue map of $R$ and whose $\varepsilon$-component is not identically zero; (iii) every $\Lambda$-algebra map $\Phi : R \to k[\varepsilon]$ with constant component the residue map has $\varepsilon$-component equal to $c$ times that of $\Phi_1$, for some $c \in k$ depending on $\Phi$. Then there is an isomorphism of $\Lambda$-algebras $e : \Lambda[[X]] \to R$ such that the $\varepsilon$-component of $\Phi_1(e(X))$ is non-zero.
--
--   This is the tangent-space form of Schlessinger's criterion recognising a formally smooth complete local $\Lambda$-algebra with one-dimensional tangent space as a power series ring in one variable, in the shape in which deformation theory supplies the hypotheses. It is obtained from the variant that produces a power series isomorphism sending $X$ to a prescribed element of the maximal ideal outside the square plus the image of $\Lambda$, and is used in the analysis of local rings on modular curves arising from level-moduli data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.exists_powerSeries_algEquiv_of_forall_exists_comp_eq_of_forall_algHom_dualNumber
    {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ]
    {R : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra Λ R] (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap Λ R)))
    (hsmooth : ∀ (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        [IsArtinianRing A] [IsArtinianRing B] [Algebra Λ A] [Algebra Λ B],
        Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap Λ A)) →
        Function.Surjective (⇑(residue B) ∘ ⇑(algebraMap Λ B)) →
        ∀ π : B →ₐ[Λ] A, Function.Surjective π →
        (∀ x ∈ RingHom.ker π, ∀ y ∈ maximalIdeal B, x * y = 0) →
        ∀ g : R →ₐ[Λ] A, ∃ g' : R →ₐ[Λ] B, π.comp g' = g)
    (Φ₁ : R →ₐ[Λ] DualNumber (ResidueField R)) (hΦ₁ : ∀ r : R, (Φ₁ r).fst = residue R r)
    (hΦ₁' : ∃ r : R, (Φ₁ r).snd ≠ 0)
    (hdim : ∀ Φ : R →ₐ[Λ] DualNumber (ResidueField R), (∀ r : R, (Φ r).fst = residue R r) →
      ∃ c : ResidueField R, ∀ r : R, (Φ r).snd = c * (Φ₁ r).snd) :
    ∃ e : PowerSeries Λ ≃ₐ[Λ] R, (Φ₁ (e PowerSeries.X)).snd ≠ 0 := by sorry
