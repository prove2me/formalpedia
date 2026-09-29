-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bbd34fc1-6036-5013-af25-e216b7d608af
-- title:
--   Transfer of h¹ and vanishing to the residue-field fibre
-- statement:
--   Let $T'$ be an Artinian local ring, $T$ a commutative ring and $\pi \colon T' \to T$ a surjective ring homomorphism whose kernel is a nilpotent ideal, and let $f_0 \colon A_0 \to \operatorname{Spec} T$ satisfy `AbelianSchemePropertyBundle`, i.e. $f_0$ is smooth and proper, every fibre $f_0^{-1}(s)$ is connected, and there exists a relative group law on $f_0$ (a functorial group structure on the sets of $T$-morphisms to $A_0$ over $\operatorname{Spec} T$, natural in the base). Assume further that for some algebraically closed field $k$, some $\rho' \colon T \to k$ and some cartesian square exhibiting $f_{k'} \colon A_{k'} \to \operatorname{Spec} k$ as the base change of $f_0$ along $\operatorname{Spec}\rho'$, the morphism $f_{k'}$ is smooth of relative dimension $g$ and $g \le \dim_k \check H^1(\mathcal K', \mathcal O_{A_{k'}})$ for some finite ordered affine cover $\mathcal K'$ of $A_{k'}$ (Čech cohomology of the presheaf $U \mapsto \Gamma(A_{k'}, U)$, the degree-$1$ value of `cechFinrank`). Let $\rho \colon T \to \operatorname{ResidueField} T'$ satisfy $\rho \circ \pi = \mathrm{residue}$, and let $f_k \colon A_k \to \operatorname{Spec}(\operatorname{ResidueField} T')$, $i_0 \colon A_k \to A_0$ form any cartesian square over $\operatorname{Spec}\rho$. Then there is $g \in \mathbb N$ such that for every finite ordered affine cover $\mathcal K$ of $A_k$ one has $g \le \dim \check H^1(\mathcal K, \mathcal O_{A_k})$ over $\operatorname{ResidueField} T'$, and $\check H^{n+1}(\mathcal K, \mathcal O_{A_k})$ (the quotient $\ker d_{n+1}/\operatorname{im} d_n$ denoted `HSucc`) is trivial for all $n \ge g$.
--
--   This is the fibre-transfer step for the good-reduction analysis of the Jacobian: a Čech bound obtained on one geometric fibre of an abelian scheme over an Artinian local thickening is moved, uniformly in the choice of cover, to the fibre over the residue field, together with vanishing in all higher degrees. It feeds the construction of the obstruction two-cocycle in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_pointDerivations_d_eq_obstruction_two_cocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (h₀ : AbelianSchemePropertyBundle T f₀)
    (hH1 : ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (Ak' : Scheme.{u}) (fk' : Ak' ⟶ Spec (CommRingCat.of k)) (i : Ak' ⟶ A₀) (ρ' : T →+* k)
      (_ : IsPullback i fk' f₀ (Spec.map (CommRingCat.ofHom ρ'))) (g : ℕ) (_ : SmoothOfRelativeDimension g fk')
      (𝒦 : Ak'.OrderedAffineCover), g ≤ (OModulePresheaf.unit fk').cechFinrank 𝒦 1)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    ∃ g : ℕ, ∀ 𝒦 : Ak.OrderedAffineCover,
      g ≤ (OModulePresheaf.unit fk).cechFinrank 𝒦 1 ∧
        ∀ n : ℕ, g ≤ n → Subsingleton ((OModulePresheaf.unit fk).HSucc 𝒦 n) := by sorry
