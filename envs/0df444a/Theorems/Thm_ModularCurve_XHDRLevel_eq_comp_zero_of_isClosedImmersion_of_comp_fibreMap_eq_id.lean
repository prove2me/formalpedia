-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id
-- name    : ModularCurve.XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/c0f44779-a76c-5319-b8b7-212f6882fcb8
-- title:
--   Uniqueness of closed-immersion sections of the fibre map
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime, $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$ and a divisibility $p \mid M$, together with a hypothesis `hj` asserting that the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios attached to the full group $\mathrm{SL}(2,\mathbb{Z})$. For a congruence subgroup $\Gamma$, let $X\,p\,\Gamma$ denote the two-chart integral model over the ring $R\,p$ of the field `qExpFunctionFieldC ℚ Γ` with respect to the element `jAt Γ hj`, with structure morphism `toBase p Γ hj` to $\mathrm{Spec}(R\,p)$. Given $\pi$ a morphism $X\,p\,(\Gamma M\,M\,H) \to X\,p\,(\Gamma N\,p\,M\,H)$ commuting with these structure morphisms, a field $\kappa$ and a ring homomorphism `toκ : R p →+* κ`, write $\mathfrak{X}_\kappa$ and $\mathfrak{X}_{0,\kappa}$ for the fibres, i.e. the pullbacks of the two structure morphisms along $\mathrm{Spec}$ of `toκ`, and `fibreMap π toκ` for the induced morphism $\mathfrak{X}_\kappa \to \mathfrak{X}_{0,\kappa}$. Assume $\mathfrak{X}_{0,\kappa}$ is integral, and that `comp : Fin 2 → (𝔛₀,κ ⟶ 𝔛κ)` is a pair of closed immersions whose images jointly cover the points of $\mathfrak{X}_\kappa$, such that `comp 0` followed by `fibreMap π toκ` is the identity, while for every endomorphism $\beta$ of $\mathfrak{X}_{0,\kappa}$ the composite $\beta$ followed by `comp 1` followed by `fibreMap π toκ` differs from the identity. Then every closed immersion $s : \mathfrak{X}_{0,\kappa} \to \mathfrak{X}_\kappa$ with $s$ followed by `fibreMap π toκ` equal to the identity satisfies $s =$ `comp 0`.
--
--   This is the rigidity step which pins down the section of the forgetful map on a geometric fibre of the level-$M$ model as the distinguished component `comp 0` (classically $\Sigma^{\infty}$), the hypothesis on `comp 1` encoding that the forgetful map restricted to the other component (classically $\Sigma^{0}$, where it is a Frobenius) admits no section. It is used in [`ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart`](thm.html#ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel NeronModelInfra
open scoped MatrixGroups

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.eq_comp_zero_of_isClosedImmersion_of_comp_fibreMap_eq_id
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj))
    (κ : Type) [Field κ] (toκ : R p →+* κ)
    [IsIntegral (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ)]
    (comp : Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ))
    (comp_isClosedImmersion : ∀ i, IsClosedImmersion (comp i))
    (comp_jointly_surjective : ∀ y : ↥(fibre (Γ := ΓM M H) (hj := hj) toκ),
      y ∈ Set.range (comp 0).base ∨ y ∈ Set.range (comp 1).base)
    (comp_pi : comp 0 ≫ fibreMap π toκ = 𝟙 _)
    (hnosec : ∀ β : fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) toκ,
      β ≫ comp 1 ≫ fibreMap π toκ ≠ 𝟙 _)
    (s : fibre (Γ := ΓN p M H hpM) (hj := hj) toκ ⟶ fibre (Γ := ΓM M H) (hj := hj) toκ)
    (hs : IsClosedImmersion s) (hsπ : s ≫ fibreMap π toκ = 𝟙 _) :
    s = comp 0 := by sorry
