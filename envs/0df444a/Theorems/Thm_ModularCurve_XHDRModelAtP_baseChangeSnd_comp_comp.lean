-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_baseChangeSnd_comp_comp
-- name    : ModularCurve.XHDRModelAtP.baseChangeSnd_comp_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/3dbf0973-bb90-5c6f-8fe2-b4b0da6031f2
-- title:
--   Component immersions commute with twists of the geometric point
-- statement:
--   Fix a prime $p$ and $M \neq 0$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$, and assume $p \mid M$ but $p^{2} \nmid M$; assume further that the $q$-expansion $j(q)$ (`jqModC ℚ`) lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which bundles a Deligne–Rapoport type model at $p$ for level $\Gamma_H(M)$: the two-chart integral models `X p (ΓM M H) hj` and `X p (ΓN p M H hpM) hj` over $\operatorname{Spec} (R\,p)$, properness, flatness, integrality, normality on affine opens, smoothness of relative dimension $1$ at the auxiliary level, a curve model of the geometric function field with its Galois compatibility and $q$-expansion pinning, and, among further data, the two morphisms $\mathfrak{X}.\mathrm{comp}\,i$ ($i \in \{0,1\}$) between the fibres. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Write $\operatorname{Spec} \kappa \to \operatorname{Spec}(R\,p)$ for the map induced by $\rho$ followed by the residue map, and let $\tau$ be an endomorphism of $\operatorname{Spec} \kappa$ over $\operatorname{Spec}(R\,p)$, that is, a scheme morphism commuting with that structure map. Then for each $i \in \{0,1\}$ the morphism $1 \times \tau$ (`RelPicard.baseChangeSnd`) on the base change of `toBase p (ΓN p M H hpM) hj` followed by $\mathfrak{X}.\mathrm{comp}\,i$ equals $\mathfrak{X}.\mathrm{comp}\,i$ followed by $1 \times \tau$ on the base change of `toBase p (ΓM M H) hj`.
--
--   This says that the two component immersions of the geometric special fibre at a prime exactly dividing the level are defined over the prime field, in the form needed as a descent hypothesis: the twisting action of endomorphisms of $\operatorname{Spec}\kappa$ on the base-changed models is compatible with the component maps. It feeds the identification of the points of the special fibre with data on the relative $\operatorname{Pic}^{0}$ used in [`ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre`](thm.html#ModularCurve.XHDRModelAtP.exists_ptsSp_gluedPic0_dictionary_specialFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_baseChangeSnd_comp_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.baseChangeSnd_comp_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (τ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) (i : Fin 2) :
    RelPicard.baseChangeSnd (toBase p (ΓN p M H hpM) hj) τ ≫ 𝔛.comp A hA ρ hρ i =
      𝔛.comp A hA ρ hρ i ≫ RelPicard.baseChangeSnd (toBase p (ΓM M H) hj) τ := by sorry
