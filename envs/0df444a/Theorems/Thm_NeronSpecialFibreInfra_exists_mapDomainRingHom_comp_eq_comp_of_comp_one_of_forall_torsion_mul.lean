-- Prove2me | Theorems.Thm_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
-- name    : NeronSpecialFibreInfra.exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e99d4a47-e76e-5bc1-9254-2f8193d87bc0
-- title:
--   Torus homomorphism induced on toric parts by Ψ_κ
-- statement:
--   Let $R$ be a commutative ring, $\kappa$ an algebraically closed field, and $\iota,\iota_0\colon\operatorname{Spec}\kappa\to\operatorname{Spec}R$ two morphisms. Let $g\colon G\to\operatorname{Spec}R$, $g_0\colon G_0\to\operatorname{Spec}R$, $f_0\colon X_0\to\operatorname{Spec}R$ carry relative group laws $L$, $L_0$, $L_{f_0}$ (functorial group structures on $T$-points over $R$, natural in $T$), and assume the base change of $f_0$ along $\iota_0$, namely $\operatorname{pullback.snd} f_0\,\iota_0$, satisfies `AbelianSchemePropertyBundle` over $\kappa$: it is smooth and proper, its fibres are connected, and it admits a relative group law. Write $G_\kappa$, $G_{0,\kappa}$, $X_{0,\kappa}$ for the base changes along $\iota$, $\iota_0$, $\iota_0$, with the base-changed group laws. Let $t,t_0\in\mathbb N$ and let $\tau\colon\operatorname{Spec}\kappa[\mathbb Z^{t}]\to G_\kappa$, $\tau_0\colon\operatorname{Spec}\kappa[\mathbb Z^{t_0}]\to G_{0,\kappa}$ be morphisms over $\kappa$ (here $\kappa[\mathbb Z^{t}]$ is `AddMonoidAlgebra κ (Fin t → ℤ)`), with $\tau_0$ a closed immersion, each multiplicative on $\kappa$-points: for all characters $\chi,\chi'$ in the monoid `WithConv` of $\kappa$-algebra maps $\kappa[\mathbb Z^{t}]\to\kappa$ (respectively $\kappa[\mathbb Z^{t_0}]\to\kappa$), the point $(\chi\chi')$ followed by $\tau$ (resp. $\tau_0$) is the group-law product of the points $\chi$ and $\chi'$ followed by $\tau$ (resp. $\tau_0$). Let $\mathrm{abq}_0,\mathrm{abq}_1\colon G_{0,\kappa}\to X_{0,\kappa}$ be morphisms over $\kappa$ which are homomorphisms on $T$-points for every $s\colon T\to\operatorname{Spec}\kappa$, and assume that a point $x$ of $G_{0,\kappa}$ over $s$ has both images equal to the unit of $L_{f_0}$ exactly when $x$ factors as $y$ followed by $\tau_0$ for some point $y$ of $\operatorname{Spec}\kappa[\mathbb Z^{t_0}]$ over $s$. Finally let $\Psi_\kappa\colon G_\kappa\to G_{0,\kappa}$ be a morphism over $\kappa$ such that for all $\kappa$-algebra maps $\chi,\chi'\colon\kappa[\mathbb Z^{t}]\to\kappa$ that are torsion, in the sense that there is $n\in\mathbb N$ with $(n:\kappa)\neq 0$ and $\chi(\mathrm{single}\,v\,1)^{n}=1$ for all $v\in\mathbb Z^{t}$ (likewise for $\chi'$), the image under $\Psi_\kappa$ of the product of the points $\tau\circ\chi$ and $\tau\circ\chi'$ over $\operatorname{Spec}\kappa$ is the product of their images. Then there exists an additive map $M_0\colon\mathbb Z^{t_0}\to\mathbb Z^{t}$ such that $\operatorname{Spec}$ of the induced ring map $\kappa[\mathbb Z^{t_0}]\to\kappa[\mathbb Z^{t}]$, followed by $\tau_0$, equals $\tau$ followed by $\Psi_\kappa$.
--
--   This is the rigidity statement that a morphism between special fibres which is multiplicative only on torsion torus points nevertheless carries the split torus $\tau$ into the split torus $\tau_0$ by a homomorphism of tori, i.e. by an integral matrix $M_0$ between the character lattices. It is the geometric input for comparing the toric parts of the special fibres of the Néron models of the Jacobians at $p$, and is used by [`ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge`](thm.html#ModularCurve.map_finPts_jHNeronObjectAtP_top_eq_and_map_toricPts_eq_of_pic0Congr_of_bridge); the proof passes through the fact that a morphism from a torus to the abelian scheme $X_{0,\kappa}$ is constant, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_comp_of_hom_spec_addMonoidAlgebra_pi_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronSpecialFibreInfra_exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem NeronSpecialFibreInfra.exists_mapDomainRingHom_comp_eq_comp_of_comp_one_of_forall_torsion_mul
    {R : Type} [CommRing R] {κ : Type} [Field κ] [IsAlgClosed κ]
    (ι ι₀ : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R))
    {G G₀ X₀ : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of R)} {g₀ : G₀ ⟶ Spec (CommRingCat.of R)}
    {f₀ : X₀ ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (L₀ : RelativeGroupLaw R g₀) (Lf₀ : RelativeGroupLaw R f₀)
    (hX₀ : AbelianSchemePropertyBundle κ (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    {t t₀ : ℕ}
    (τ : SchemeHomOver (torusStr κ t) (RelativeGroupLaw.baseChangeStr ι g))
    (hτmul : ∀ χ χ' : WithConv (torusCoord κ t →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
        (L.baseChange ι).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ))
    (τ₀ : SchemeHomOver (torusStr κ t₀) (RelativeGroupLaw.baseChangeStr ι₀ g₀)) (hτ₀ : IsClosedImmersion τ₀.1)
    (hτ₀mul : ∀ χ χ' : WithConv (torusCoord κ t₀ →ₐ[κ] κ),
      NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ₀ =
        (L₀.baseChange ι₀).mul _ (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ₀)
          (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ₀))
    (abq₀ : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr ι₀ g₀) (RelativeGroupLaw.baseChangeStr ι₀ f₀))
    (abq₀_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      NeronModelInfra.schemeHomOverComp ((L₀.baseChange ι₀).mul s x y) (abq₀ i) =
        (Lf₀.baseChange ι₀).mul s (NeronModelInfra.schemeHomOverComp x (abq₀ i))
          (NeronModelInfra.schemeHomOverComp y (abq₀ i)))
    (abq₀_eq_one_iff : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of κ))
      (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr ι₀ g₀)),
      (∀ i, NeronModelInfra.schemeHomOverComp x (abq₀ i) = (Lf₀.baseChange ι₀).one s) ↔
        ∃ y : SchemeHomOver s (torusStr κ t₀), NeronModelInfra.schemeHomOverComp y τ₀ = x)
    (Ψκ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι₀ g₀))
    (hΨκ_mul : ∀ χ χ' : torusCoord κ t →ₐ[κ] κ,
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ (AddMonoidAlgebra.single v 1) ^ n = 1) →
      (∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ v : Fin t → ℤ, χ' (AddMonoidAlgebra.single v 1) ^ n = 1) →
      NeronModelInfra.schemeHomOverComp ((L.baseChange ι).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ)) Ψκ =
        (L₀.baseChange ι₀).mul (𝟙 _)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ) τ) Ψκ)
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (torusPt κ t χ') τ) Ψκ)) :
    ∃ M₀ : (Fin t₀ → ℤ) →+ (Fin t → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ M₀)) ≫ τ₀.1 = τ.1 ≫ Ψκ.1 := by sorry
