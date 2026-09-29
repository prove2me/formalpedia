-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
-- name    : ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4aaaff84-697e-56ec-bdbc-b7392a768da3
-- title:
--   Residue-field rationality of crossing points on the O-model
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$; assume $M/p \neq 0$ in the relevant sense and that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field $\mathbb{Q}$-subfield `qExpFunctionFieldC ℚ ⊤` attached to the full modular group. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport model datum at $p$ for the level $\Gamma_H(M)$ curve over the base ring `R p`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa_A$ is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $\mathrm{R}\,p \to \overline{\mathbb{Q}}$. Let $O$ be a local commutative ring with a homomorphism $\rho_O : \mathrm{R}\,p \to O$, and let $\mathrm{to}\kappa : O \to \kappa_A$ be a surjective ring homomorphism with $\mathrm{to}\kappa \circ \rho_O$ equal to the residue map of $A$ composed with $\rho$. Then for every point $n$ of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` (the crossings of the geometric special fibre at $A$) there is a morphism $s$ from $\operatorname{Spec}$ of the residue field $O/\mathfrak{m}_O$ to the base change `XO (ΓM M H) hj ρO`, the pullback of the structure morphism `toBase p (ΓM M H) hj` along $\operatorname{Spec}$ of $\rho_O$, such that $s$ followed by the projection to $\operatorname{Spec} O$ is $\operatorname{Spec}$ of the residue homomorphism $O \to O/\mathfrak{m}_O$, and such that $s$ sends the closed point of $\operatorname{Spec}(O/\mathfrak{m}_O)$ to the crossing point `𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n`, that is, to the image of $n$ under the first projection followed by `𝔛.comp A hA ρ hρ 0` and the base-change map `bcMap (ΓM M H) hj ρO toκ htoκ`.
--
--   The statement supplies the rationality input needed to construct oriented étale charts at the crossings of the Deligne–Rapoport model of $X_H(M)$ over a local base $O$: each crossing point of the special fibre is visible as an $O/\mathfrak{m}_O$-point of the $O$-model whenever $O$ surjects onto the residue field $\kappa_A$, as happens for the valuation ring of the inertia field of $A$. It is used in the analysis of widths and slopes at the crossings, notably by the results producing a section with unit slope law at a crossing and an annulus of prescribed width attached at both ends.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.forall_exists_spec_residueField_hom_comp_snd_eq_and_base_closedPoint_eq_crossingPt_of_surjective
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsLocalRing O] (ρO : R p →+* O)
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (hsurj : Function.Surjective toκ) :
    ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ XO (ΓM M H) hj ρO,
        s ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ∧
        s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) = 𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n := by sorry
