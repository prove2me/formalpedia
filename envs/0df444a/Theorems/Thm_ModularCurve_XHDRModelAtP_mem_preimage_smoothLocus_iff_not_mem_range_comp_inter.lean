-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
-- name    : ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/62738b41-fcca-5788-b666-1a6ede792a6c
-- title:
--   Smooth locus criterion on the special fibre of X_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, together with hypotheses $p \mid M$ and $p^2 \nmid M$, and assume $j$'s $q$-expansion `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, that is, the two-chart integral model $X =$ `X p (ΓM M H) hj` over $R_p$ together with the bundled data and properties recorded in that structure: properness, flatness, integrality, local finite presentation and normality of the structure morphism `toBase p (ΓM M H) hj`, properness and smoothness of relative dimension $1$ at level `ΓN p M H hpM`, a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` identified with the geometric generic fibre by an isomorphism `eeta` compatible with the Galois action and pinned on $q$-expansions, generic smoothness and geometric integrality, and the further fields of the structure (summarised here), among them an open `𝔛.smoothLocus` of $X$ and the morphisms `𝔛.comp`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`A.LiesOverPrime p`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Then for every point $y$ of the geometric special fibre `fibre ((residue A).comp ρ)`, the pullback of $X$ along $\operatorname{Spec} \kappa \to \operatorname{Spec} R_p$, the point $y$ lies in the preimage of `𝔛.smoothLocus` under the first projection of that pullback if and only if it is not the case that $y$ lies both in the image of the underlying map of `𝔛.comp A hA ρ hρ 0` and in the image of the underlying map of `𝔛.comp A hA ρ hρ 1`.
--
--   This is the Deligne–Rapoport description of the model of $X_H(M)$ at a prime $p$ exactly dividing $M$: the smooth locus of the model over the base meets the geometric special fibre precisely in the complement of the intersection of the two components, i.e. away from the crossing points. It is used in the analysis of the Néron model and of the component group attached to $J_H$ at $p$, where divisors and Picard classes on the special fibre are computed component by component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : ↥(fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))) :
    y ∈ (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) ↔
      ¬ (y ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧ y ∈ Set.range (𝔛.comp A hA ρ hρ 1).base) := by sorry
