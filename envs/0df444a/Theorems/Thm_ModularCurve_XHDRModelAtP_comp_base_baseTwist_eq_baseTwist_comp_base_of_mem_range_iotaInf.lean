-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
-- name    : ModularCurve.XHDRModelAtP.comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/03dde9c9-2d5b-5f73-8e13-18dab2e5dc5d
-- title:
--   Component maps commute with a residual base twist at pole-chart points
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p \mid M$ and $M/p$ nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a witness $hj$ that the Laurent series $j$-expansion `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios for $\mathrm{SL}(2,\mathbb{Z})$. Let $\mathfrak{X}$ be an instance of the structure `XHDRModelAtP p M H hpM hj`, which packages an integral model over `R p` of the modular curve at level `ΓM M H` (proper, flat, integral, with integrally closed sections on affine opens), a smooth proper model at level `ΓN p M H hpM`, a curve model over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` identified with the generic geometric fibre compatibly with the Galois action and with $q$-expansions, and further data including the morphisms $\mathfrak{X}.\mathrm{comp}$ used below. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : \mathtt{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Write $\kappa$ for the residue field of $A$ and $\bar\rho = \mathrm{residue} \circ \rho$; for a subgroup $\Gamma$, `fibre` denotes the pullback of `toBase p Γ hj` along $\operatorname{Spec} \bar\rho$. Let $\psi$ be a ring automorphism of $\kappa$ with $\psi \circ \bar\rho = \bar\rho$, and let $\Xi_N$, $\Xi_M$ be endomorphisms of the `ΓN p M H hpM`- and `ΓM M H`-fibres respectively, each commuting with the first projection and satisfying: the endomorphism followed by the second projection equals the second projection followed by $\operatorname{Spec}\psi$. Let $z$ be a point of the `ΓN`-fibre such that the image of $(\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,0)(z)$ under the first projection lies in the range of the underlying map of `ιInf p (ΓM M H) hj`, the chart of the model away from the zero locus of $j$. Then for each $i \in \{0,1\}$ one has, on underlying topological spaces, $(\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i)(\Xi_N(z)) = \Xi_M\bigl((\mathfrak{X}.\mathrm{comp}\,A\,hA\,\rho\,h\rho\,i)(z)\bigr)$.
--
--   This records that the two morphisms from the level-$\Gamma_N$ fibre into the fibre at level $\Gamma_H(M) \cap \Gamma_0(p)$ — the two components of the Deligne–Rapoport special fibre — are insensitive to twisting the base by an automorphism $\psi$ of the residue field fixing the image of the coefficient ring, at least at points whose image lies in the chart where $j$ is invertible. It is used in the analysis of reduction of points and Frobenius twists on the Néron object at $p$, being cited by [`ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction`](thm.html#ModularCurve.JHNeronObjectAtP.ptsSp_symm_frobeniusTwist_eq_glueMap_of_pointReduction).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing
  ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.comp_base_baseTwist_eq_baseTwist_comp_base_of_mem_range_iotaInf
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
    (hψ : ψ.toRingHom.comp ((IsLocalRing.residue ↥A).comp ρ) = (IsLocalRing.residue ↥A).comp ρ)

    (ΞN : (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hΞN₁ : ΞN ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞN₂ : ΞN ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))
    (ΞM : (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)) ⟶
      (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hΞM₁ : ΞM ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞM₂ : ΞM ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom))

    (z : ↥(fibre (Γ := XHDRLevel.ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (hz : (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.comp A hA ρ hρ 0).base z) ∈ Set.range (ιInf p (ΓM M H) hj).base)
    (i : Fin 2) :
    (𝔛.comp A hA ρ hρ i).base (ΞN.base z) = ΞM.base ((𝔛.comp A hA ρ hρ i).base z) := by sorry
