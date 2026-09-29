-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
-- name    : ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/0bfda5f1-bddc-5c91-87ce-ed2a6e7ef92c
-- title:
--   Euler characteristics of ± a C_c twists on the resolved model
-- statement:
--   Fix a nonzero natural number $N₀$ and a prime $p$ with $p \nmid N₀$, a Deligne–Rapoport model package `𝔓` of level $N₀p$, a commutative ring $O$ with a ring homomorphism $ρO$ from `DRLevel.R p` to $O$, an algebraically closed field $κ$ of characteristic $p$ with a ring homomorphism $toκ : O \to κ$, and a resolved package $R$ of type `DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ`, whose scheme `R.Y` carries the component ideal sheaves `R.comp v` indexed by $v \in$ `X0MqComponents R.width` $= \mathrm{Fin}\,2 \sqcup \coprod_{n}\mathrm{Fin}(R.\mathrm{width}\,n-1)$. Let $c$ be such an index, $k$ a field, and $y$ a proper morphism from the closed subscheme cut out by `R.comp c` to $\operatorname{Spec} k$, and assume that for every node $n$ and every $d : \mathrm{Fin}(R.\mathrm{width}\,n)$ whose point `R.edgePt n d` lies in the support of `R.comp c` there is a section $s$ of $y$ (that is, $s$ followed by $y$ is the identity) whose composite with the closed immersion `(R.comp c).subschemeι` has `R.edgePt n d` in the range of its underlying map. Let $M$ be a module on `R.Y` that is invertible in the sense that every point has an open neighbourhood on which the restriction of $M$ is isomorphic to the unit module, let $a$ be a natural number, and let $𝒲$ consist of two affine opens of the subscheme covering it and with affine intersection. For a module $N$ on the subscheme write $\chi(N) = \dim_k H^0 - \dim_k H^1$ of the two-term Čech complex `𝒲.sectionsOf y N` (sections over the two opens, differential the difference of the two restrictions to the intersection). Then, with $\iota =$ `(R.comp c).subschemeι` and $I =$ `R.comp c`, writing $I^a.\mathrm{module}$ for the $a$-th power ideal sheaf viewed as a module and $I^a.\mathrm{invModule}$ for its dual,
--   $$\chi\bigl(\iota^*((I^a)^\vee \otimes M)\bigr) = \chi(\iota^*M) - a\sum_{F \ne c}\mathrm{x0MqAdj}(R.\mathrm{width})(F,c), \qquad \chi\bigl(\iota^*(I^a \otimes M)\bigr) = \chi(\iota^*M) + a\sum_{F \ne c}\mathrm{x0MqAdj}(R.\mathrm{width})(F,c),$$
--   the sums being over all component indices other than $c$ and `x0MqAdj` being the explicit adjacency of the subdivided dual graph: between the two strict-transform indices it is the number of nodes of width $1$, between a strict transform and a chain vertex it is $1$ exactly at the two ends of the chain, and between two chain vertices it is $1$ for consecutive positions in the same chain.
--
--   This is the Čech-complex form of the self-intersection computation on a regular model with reduced special fibre $\sum_F C_F$ satisfying $\prod_F \mathfrak c_F = (p)$: twisting by $\mathcal O(\pm a C_c)$ and restricting to $C_c$ changes the Euler characteristic by $\mp a\,(C_c\cdot\sum_{F\neq c}C_F)$, the number of neighbours of $c$ in the dual graph counted with multiplicity. It feeds the computation of Euler characteristics of kernels of the maps to products of component sheaves on the resolved Deligne–Rapoport model of $X_0(N_0p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra MazurRapoportAppendix
open ModularCurve
open scoped BigOperators

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_pow_comp_invModule_tensor_and_module_tensor_self
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] {ρO : DRLevel.R p →+* O}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    (c : X0MqComponents R.width)
    {k : Type} [Field k] (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of k)) [IsProper y]
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)), R.edgePt n d ∈ (R.comp c).support →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (M : R.Y.Modules) (hM : Scheme.Modules.IsInvertible M) (a : ℕ) (𝒲 : ((R.comp c).subscheme).TwoAffineOpenCover) :
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).invModule ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).invModule ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H1
        - (a : ℤ) * ∑ F ∈ Finset.univ.erase c, (x0MqAdj R.width F c : ℤ)) ∧
    ((Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).module ⊗ M))).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj (((R.comp c) ^ a).module ⊗ M))).H1
      = (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H0 : ℤ)
        - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj M)).H1
        + (a : ℤ) * ∑ F ∈ Finset.univ.erase c, (x0MqAdj R.width F c : ℤ)) := by sorry
