-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_preimage_closure_image_range_comp_eq_of_comp_fst_eq
-- name    : ModularCurve.XHDRModelAtP.preimage_closure_image_range_comp_eq_of_comp_fst_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/10ee0f95-6285-58d6-a414-65353f848833
-- title:
--   Special-fibre components are saturated for the comparison map
-- statement:
--   Fix a prime $p$ and $M \geq 1$ with $p \mid M$ but $p^{2} \nmid M$, a subgroup $H \leq (\mathbb{Z}/M)^{\times}$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^{\times}$, and assume $M/p \neq 0$ in the relevant sense; assume the $q$-expansion `jqModC` of $j$ lies in the intermediate field `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}$-rational $q$-expansions for $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be a term of the project's structure `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport data bundle for the model of $X_H(M)$ over $R\,p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : R\,p \to A$ be a ring map compatible with $R\,p \to \overline{\mathbb{Q}}$. Let $O$ be a commutative ring with maps $\rho_O : R\,p \to O$ and $O \to \kappa_A$ whose composite with $\rho_O$ is the residue map composed with $\rho$. Let $bc$ be any scheme morphism from the fibre of `toBase` over $\kappa_A$ to the project's $O$-model `XO`, subject only to commuting with the two first projections to the model. Then for each $i \in \{0,1\}$, the preimage under $bc$ of the closure of the image of the range of the base map of $\mathfrak{X}.\mathrm{comp}\ A\ hA\ \rho\ h\rho\ i$ — the $i$-th component of the geometric special fibre — equals that range itself.
--
--   The statement expresses that each of the two components of the geometric special fibre of $X_H(M)$ at a place above $p$ is saturated for any morphism to the $O$-model commuting with the projections to the model: no point off the component can map into the closure of its image. It feeds the determination of the local ring at a crossing point in [`ModularCurve.XHDRModelAtP.exists_maximalIdeal_eq_branchIdeal_sup_span_singleton`](thm.html#ModularCurve.XHDRModelAtP.exists_maximalIdeal_eq_branchIdeal_sup_span_singleton), via the existence of two distinct minimal primes of $(p)$ in the $j$-finite chart ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_preimage_closure_image_range_comp_eq_of_comp_fst_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.preimage_closure_image_range_comp_eq_of_comp_fst_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] (ρO : R p →+* O)
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ XO (ΓM M H) hj ρO)
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _) (i : Fin 2) :
    bc.base ⁻¹' closure (bc.base '' Set.range (𝔛.comp A hA ρ hρ i).base) = Set.range (𝔛.comp A hA ρ hρ i).base := by sorry
