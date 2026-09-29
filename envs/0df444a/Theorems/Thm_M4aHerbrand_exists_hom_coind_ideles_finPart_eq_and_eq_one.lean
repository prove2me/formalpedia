-- Prove2me | Theorems.Thm_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one
-- name    : M4aHerbrand.exists_hom_coind_ideles_finPart_eq_and_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/374258c1-aed6-5dea-86e7-4637159550a0
-- title:
--   Coinduced local units map into the idèles, with coordinate pins
-- statement:
--   Let $E \subseteq K$ be number fields with $K/E$ Galois, $G = \mathrm{Gal}(K/E)$, let $D$ be a datum of the project's structure `IdeleGaloisDescent` for $(\mathcal O_K, E, K)$, i.e. a monoid homomorphism $D.\mathrm{act}$ from $G$ to the ring automorphisms of the adèle ring $\mathbb A_K$ which is continuous for each $g$ and compatible with the structure map $K \to \mathbb A_K$, and suppose the ambient `MulDistribMulAction` of $G$ on $\mathbb A_K^\times$ is the one induced by $D$ through `unitsAct`. Let $v_0$ be a height-one prime of $\mathcal O_E$ and put $w_1 =$ [`NumberField.PlaceAbove.above E K v₀`](def/NumberField_PlaceAbove.html#L27), the chosen prime of $\mathcal O_K$ over $v_0$, with decomposition subgroup $G_{w_1} \le G$ (the decomposition subgroup of the valuation subring of the $w_1$-adic valuation). Then there is a morphism $\mathrm{Sh}$ of representations from $\mathrm{Coind}_{G_{w_1}}^{G}$ of the $G_{w_1}$-module $(K_{w_1})^\times$ (written additively) to the $G$-module $(\mathbb A_K)^\times$ such that for every element $f$ of the coinduced module: the $w_1$-component of $\mathrm{Sh}(f)$, i.e. its image under `finPart`, equals $f(1)$; the $w$-component is $1$ for every height-one prime $w$ of $\mathcal O_K$ whose contraction along $\mathcal O_E \to \mathcal O_K$ differs from $v_0$; and the archimedean part `infPart` of $\mathrm{Sh}(f)$ is $1$. No injectivity or surjectivity of $\mathrm{Sh}$ is asserted, only equivariance together with these three coordinate identities.
--
--   This is the Shapiro-type comparison map used to realise classes of the coinduced module of local units at the chosen place above $v_0$ as explicit idèles supported above $v_0$; the coordinate identities pin the construction at the level of cochains. It feeds the construction of two-cocycles valued in the idèles with prescribed support, [`M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero`](thm.html#M4aHerbrand.exists_two_cocycle_ideles_mem_unitIdelesOutside_and_map_prG_eq_zsmul_and_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_exists_hom_coind_ideles_finPart_eq_and_eq_one.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 400000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem M4aHerbrand.exists_hom_coind_ideles_finPart_eq_and_eq_one
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : (K ≃ₐ[E] K)) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (v₀ : HeightOneSpectrum (𝓞 E)) :
    ∃ Sh : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ) ⟶
        Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      (∀ f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ),
        finPart (NumberField.PlaceAbove.above E K v₀) (Additive.toMul (Sh.hom f)) = Additive.toMul (f.1 1)) ∧
      (∀ (f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ))
        (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v₀.asIdeal →
        finPart w (Additive.toMul (Sh.hom f)) = 1) ∧
      (∀ f : Rep.coind (NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)).subtype (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v₀)) ((NumberField.PlaceAbove.above E K v₀).adicCompletion K)ˣ),
        infPart (Additive.toMul (Sh.hom f)) = 1) := by sorry
