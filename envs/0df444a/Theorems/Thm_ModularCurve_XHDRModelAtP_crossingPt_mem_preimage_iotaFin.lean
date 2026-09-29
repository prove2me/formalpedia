-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin
-- name    : ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/a7ca0056-d983-5c30-a716-d79e563c9a19
-- title:
--   Crossing points lie in the finite-j chart
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ but $p^2 \nmid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial, with $M/p$ again nonzero, and let `hj` record that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤` generated over $\mathbb{Q}$ by ratios of integral $q$-expansions of modular forms of level $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be a Deligne–Rapoport package `XHDRModelAtP p M H hpM hj` for the two-chart integral model `X p (ΓM M H) hj` over `R p`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field has characteristic $p$ and is algebraically closed, and let $\rho : R p \to A$ be a ring homomorphism compatible with the structural map $R p \to \overline{\mathbb{Q}}$. Let $O$ be a commutative ring with a homomorphism $\rho_O : R p \to O$ and a homomorphism $\mathrm{to}\kappa : O \to \kappa_A$ to the residue field of $A$ with $\mathrm{to}\kappa \circ \rho_O$ equal to $\rho$ followed by the residue map. Finally, let $n$ be a point of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` provided by $\mathfrak{X}$. Then the image of the associated point `𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n` of the base change $X_O$ under the first projection to `X p (ΓM M H) hj` lies in the image of the base map of the finite-$j$ chart immersion `ιFin p (ΓM M H) hj`.
--
--   This says that a crossing of the special fibre of the Deligne–Rapoport model of $X_H(M)$ is visible in the chart where $j$ is regular, i.e. that crossings are supersingular points rather than cusps. It is used in the subsequent analysis of the crossing points, in particular in locating a prime of the finite chart at a crossing, in the stalk computations at crossings, and in the construction of configured representations attached to the Néron model at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_crossingPt_mem_preimage_iotaFin.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.crossingPt_mem_preimage_iotaFin
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] (ρO : R p →+* O)
    (toκ : O →+* IsLocalRing.ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))).base (𝔛.crossingPt A hA ρ hρ ρO toκ htoκ n) ∈ Set.range (ιFin p (ΓM M H) hj).base := by sorry
