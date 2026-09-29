-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/c5c66417-57dd-5f81-a488-e320cd744ebf
-- title:
--   Finite order of sheaf-preserving automorphisms over a finite field
-- statement:
--   Let $k_0$ be a finite field, $A$ a scheme and $f : A \to \operatorname{Spec} k_0$ a morphism satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and a relative group law on the functor of points of $f$ exists. Let $M$ be a module over the structure sheaf of $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ on which the restriction of $M$ is isomorphic to the unit module of $U$; assume further that `ClosedImmersionBySections M f` holds, i.e. for some $N$ there are $N+1$ global sections of $M$ and a morphism $A \to \operatorname{Proj}$ of the polynomial ring in $N+1$ variables over $k_0$, lying over $f$, such that each section frames $M$ freely over the preimage of the corresponding standard basic open and the sections transform into one another by the coordinate ratios, and such that this morphism is a closed immersion. Let $\sigma$ be a morphism $A \to A$ with $\sigma \circ\! f$-compatibility $\sigma \mathbin{;} f = f$, whose underlying scheme morphism is an isomorphism, and suppose every point of $\operatorname{Spec} k_0$ has an open neighbourhood $U$ over which the restrictions of $\sigma^{*}M$ and of $M$ to $f^{-1}(U)$ are isomorphic. Then there is $m \neq 0$ with the $m$-fold iterate of $\sigma$ equal to the identity morphism of $A$ over $f$. Of the clauses of `AbelianSchemePropertyBundle`, the proof uses only properness of $f$.
--
--   This is the finite-field case of the finiteness of the automorphism group of a polarised abelian variety, in the weak form 'every automorphism preserving the polarising invertible sheaf has finite order', obtained without the Rosati involution and with no homomorphism hypothesis on $\sigma$. It is the input to the corresponding statement for a polarised abelian scheme over an algebraically closed field, [`AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_pol_iso_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.PolarisedAbelianScheme

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_schemeHomOverNpow_eq_schemeHomOverId_of_isIso_of_pullback_iso_of_finite
    {k₀ : Type} [Field k₀] [Finite k₀]
    {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of k₀)} (hA : AbelianSchemePropertyBundle k₀ f)
    (M : A.Modules) (hM : Scheme.Modules.IsInvertible M) (hci : Scheme.Modules.ClosedImmersionBySections M f)
    (σ : SchemeHomOver f f) (hσiso : IsIso σ.1)
    (hpol : ∀ s : ↥(Spec (CommRingCat.of k₀)), ∃ U : (Spec (CommRingCat.of k₀)).Opens, s ∈ U ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback σ.1).obj M) ≅
        (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M)) :
    ∃ m : ℕ, m ≠ 0 ∧ NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId f := by sorry
