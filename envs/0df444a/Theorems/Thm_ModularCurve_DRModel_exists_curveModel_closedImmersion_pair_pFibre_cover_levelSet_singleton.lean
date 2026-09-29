-- Prove2me | Theorems.Thm_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
-- name    : ModularCurve.DRModel.exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7d783d0b-969c-5d11-823c-66096fda5f3c
-- title:
--   Fibre at p of the Deligne–Rapoport model: two lines
-- statement:
--   Let $p$ be a prime and let $\kappa$ be an algebraically closed field of characteristic $p$. Write $X_\kappa$ for the fibre product of `DRModel.toBase p` with $\operatorname{Spec}\kappa\to\operatorname{Spec}\mathbf Z$, where `DRModel p` is the two-chart integral model over $\mathbf Z$ of the element `IgusaScheme.jFull p` of `modularFunctionFieldFull p` (the subfield of $\mathbf Q((q))$-Laurent series generated over $\mathbf Q$ by the divisor expansions of level $p$), namely the pushout of its finite and infinite charts, with `toBase` the map descended from $\operatorname{Spec}$ of the two structure maps from $\mathbf Z$. The theorem asserts the existence of a `CurveModel κ (RatFunc κ)` $M$ — an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec}\kappa$, with a ring isomorphism $\kappa(t)\cong$ the function field of $M.C$ compatible with $\kappa$, a bijection of the closed points of $M.C$ with the places of $\kappa(t)/\kappa$ carrying the image of each stalk onto the corresponding valuation subring, and every finite set of points inside an affine open — together with two morphisms $c_\infty,c_0\colon M.C\to X_\kappa$ such that: each followed by the second projection is $M.toBase$; each is a closed immersion; every point of $X_\kappa$ lies in the range of $c_\infty$ or of $c_0$ on underlying spaces; each range contains a point outside the other; for every $c\in\kappa$ there is a closed point $x$ of $M.C$ with the complement of the open set `jNeLocus … c` (the union of the basic open where the finite $j$-coordinate differs from $c$ and the basic open where $1-c\cdot j^{-1}$ is invertible) meeting the range of $c_\infty$ exactly in $\{c_\infty(x)\}$, and likewise for $c_0$; and, finally, the complement of the preimage `chartFinOpenBC` of the finite chart meets each of the two ranges in a single point, again the image of a closed point of $M.C$.
--
--   This is the set-theoretic content, over an algebraically closed field of characteristic $p$, of the Deligne–Rapoport description of the bad fibre of the integral model of $X_0(p)$: two copies of the projective $j$-line, mapping to the $j$-line by $j$ and by its Frobenius twist, glued at the supersingular points. Only what the later level-set analysis needs is recorded — a cover of the fibre by two closed curves with mutually incomparable images, each meeting every level locus $j=c$ ($c\in\kappa$) and the cusp locus $j=\infty$ in exactly one closed point — and it is used in this form by [`ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton`](thm.html#ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve

theorem ModularCurve.DRModel.exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton
    (p : ℕ) [Fact p.Prime] [NeZero p] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] :
    ∃ (M : CurveModel κ (RatFunc κ))
      (cInf cZero : M.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
      cInf ≫ pullback.snd _ _ = M.toBase ∧ cZero ≫ pullback.snd _ _ = M.toBase ∧
      IsClosedImmersion cInf ∧ IsClosedImmersion cZero ∧
      (∀ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cInf.base ∨ x ∈ Set.range cZero.base) ∧
      (∃ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cInf.base ∧ x ∉ Set.range cZero.base) ∧
      (∃ x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))),
          x ∈ Set.range cZero.base ∧ x ∉ Set.range cInf.base) ∧
      (∀ c : κ, ∃ x : closedPoints M.C,
        ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range cInf.base =
          {cInf.base x.1}) ∧
      (∀ c : κ, ∃ x : closedPoints M.C,
        ((TwoChartIntegralModel.jNeLocus ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ c :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range cZero.base =
          {cZero.base x.1}) ∧
      (∃ x : closedPoints M.C,
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range cInf.base =
          {cInf.base x.1}) ∧
      (∃ x : closedPoints M.C,
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ).Opens) :
        Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) κ))ᶜ ∩ Set.range cZero.base =
          {cZero.base x.1}) := by sorry
