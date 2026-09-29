-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_inclusion_mem_igusaRing_and_inv_mem_of_residue_ne_zero
-- name    : ModularCurve.FullLevel.inclusion_mem_igusaRing_and_inv_mem_of_residue_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/ab171888-c650-51c7-89b4-d79e67a47274
-- title:
--   Integral level-M' functions with non-zero reduction are Igusa units
-- statement:
--   Fix a prime $q$ and $M'\ge 1$ with $q\nmid M'$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, and an inclusion `hle` of the intermediate field $\overline{\mathbb{Q}}\,$-base change `modularFunctionFieldBar M'` of the full level-$M'$ modular function field into `fieldBar q M'`, both viewed inside $\overline{\mathbb{Q}}((t))$. Let $R_0$ be a `ConstantReduction` of `modularFunctionFieldBar M'` over $A$ with values in `modularFunctionFieldC (ResidueField A) M'` — a valuation subring $R_0.\mathrm{integers}$, a surjective residue map onto that field with kernel the maximal ideal, compatible with $A$ and with a degree-preserving map on places — and assume $R_0$ is realised coefficientwise: for each Laurent series $y$ over $A$ whose coefficientwise image lies in `modularFunctionFieldBar M'`, that element is $R_0$-integral and its residue, read as a Laurent series over the residue field of $A$, is the coefficientwise reduction of $y$. Let $\zeta$ be a primitive $q$-th root of unity in $\overline{\mathbb{Q}}$ and let $\ell\mapsto \mathcal{O}^{\mathrm{Ig}}_\ell$ assign a valuation subring of `fieldBar q M'` to each point of $\mathbb{P}^1(\mathbb{F}_q)$, subject to: $\mathcal{O}^{\mathrm{Ig}}_{\infty}$ (at the point $[1:0]$) consists of the $f$ for which there are Laurent series $x,y$ over $A$ with $y$ of non-zero coefficientwise reduction and $f\cdot y=x$; and each $\ell$ is $\mathrm{redQ}(\gamma)\cdot\infty$ for some $\gamma\in\Gamma_0(M')$ with $\mathcal{O}^{\mathrm{Ig}}_\ell$ the pullback of $\mathcal{O}^{\mathrm{Ig}}_{\infty}$ along `levelAutBar q M' ζ γ`. Then for every $g$ in `modularFunctionFieldBar M'` that is $R_0$-integral with non-zero $R_0$-residue, the image of $g$ in `fieldBar q M'` and its inverse both lie in $\mathcal{O}^{\mathrm{Ig}}_\ell$ for every $\ell\in\mathbb{P}^1(\mathbb{F}_q)$.
--
--   This says that a level-$M'$ function of Gauss norm one with non-zero reduction is a unit at the Gauss point of every component of the Igusa-type configuration, the case $\ell=\infty$ being the Gauss ring at the cusp and the remaining cases obtained by transport along the level automorphisms attached to $\Gamma_0(M')$, which carry level-$M'$ $q$-expansions to $q$-twisted ones. It is used in the analysis of the node charts and local stalks of the normal model of the full-level modular curve in residue characteristic $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_inclusion_mem_igusaRing_and_inv_mem_of_residue_ne_zero.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.inclusion_mem_igusaRing_and_inv_mem_of_residue_ne_zero
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (g : ↥(modularFunctionFieldBar M')) (hg : g ∈ R₀.integers) (hgne : R₀.residue ⟨g, hg⟩ ≠ 0) :
    ∀ ℓ : CuspidalType.ProjLine q,
      (IntermediateField.inclusion hle g : ↥(fieldBar q M')) ∈ OIg ℓ ∧
      (IntermediateField.inclusion hle g : ↥(fieldBar q M'))⁻¹ ∈ OIg ℓ := by sorry
