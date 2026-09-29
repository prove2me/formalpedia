-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
-- name    : ModularCurve.XHDRModelAtP.exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/7ece0316-bcd4-5eff-9e24-21450453ce4d
-- title:
--   Formal unramifiedness of π near a section off the crossings
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbf{Z}/M)^{\times}$, and the hypothesis `hj` that the Laurent series $j(q)$ over $\mathbf{Q}$ lies in the $q$-expansion function field of the full modular group; let $\mathfrak{X}$ be an instance of the bundle `XHDRModelAtP p M H hpM hj`, which packages the two-chart integral model $X$ of level $\Gamma_M(H)$ over $R_p$ (its structure morphism proper, flat, of locally finite presentation, with $X$ integral and normal on affines), the smooth proper model at level $\Gamma_N(p,M,H)$, a curve model `Meta` over $\overline{\mathbf{Q}}$ for the function field $\overline{X_H(M)}$ identified by `eeta` with the geometric generic fibre, compatibly with the Galois action and pinned on $q$-expansions, together with a forgetful morphism `π`. Let $A$ be a valuation subring of $\overline{\mathbf{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbf{Q}}$ is the structure map. Let $y$ be a $\overline{\mathbf{Q}}$-point of `Meta.C` over $\operatorname{Spec}\overline{\mathbf{Q}}$, and $u$ a morphism $\operatorname{Spec} A \to X$ lying over $\operatorname{Spec}\rho$, whose restriction along $A \hookrightarrow \overline{\mathbf{Q}}$ agrees with $y$ transported to $X$ by `eeta` and the first projection (hypothesis `hu`). Let $u\kappa$ be a morphism from $\operatorname{Spec}$ of the residue field of $A$ to the fibre of the model over the composite $R_p \to A \to \kappa$, i.e. the pullback of the structure morphism, whose first projection is $u$ reduced modulo the maximal ideal and whose second projection is the identity. Finally let $P$ be a closed point of the curve $\mathfrak{X}.\mathrm{Mfib}$ attached to $A, \rho$ such that the image of $P$ under `𝔛.efib` followed by the zeroth component map `𝔛.comp … 0` is the image under $u\kappa$ of the closed point of the residue field (hypothesis `hP`), and such that the place of the $q$-expansion function field at level $\Gamma_N(p,M,H)$ over the residue field attached to $P$ differs from $\mathfrak{X}.\mathrm{placeOn0}\,n$ for every point $n$ of the pullback of the two component maps `𝔛.comp … 0` and `𝔛.comp … 1`, where $\mathrm{placeOn0}\,n$ is the $p$-Frobenius twist of the supersingular $q$-expansion place given by $\mathfrak{X}.\mathrm{nodeEquiv}\,n$. Then there exists an open subscheme $V$ of $X$ containing the set-theoretic image of $u$ such that the inclusion of $V$ followed by the underlying morphism of $\mathfrak{X}.\pi$ is formally unramified.
--
--   This is the local statement, in the style of the Deligne–Rapoport description of the special fibre, that the forgetful map between the two levels is formally unramified along any $A$-valued section whose reduction meets the component indexed by $0$ at a point that is not one of the crossing (supersingular) points. It is used, together with the comparison of ramification indices along the degeneracy embedding, in the divisor pull-back computations [`ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow`](thm.html#ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow) and in the corresponding point-counting statement at the Néron model level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_opens_formallyUnramified_pi_of_comp_zero_of_forall_ne_placeOn0
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ V : (X p (ΓM M H) hj).Opens, Set.range u.1.base ⊆ (V : Set (X p (ΓM M H) hj)) ∧
      FormallyUnramified (V.ι ≫ 𝔛.π.1) := by sorry
