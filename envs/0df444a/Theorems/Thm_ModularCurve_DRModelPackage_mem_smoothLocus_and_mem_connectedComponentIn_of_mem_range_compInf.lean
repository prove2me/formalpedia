-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
-- name    : ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/926524c5-d832-55ae-a300-832a5c923c65
-- title:
--   Fibre points off the 0-component: smooth, in the cusp component
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a term of the structure `DRModelPackage p`, which bundles over the two-chart integral model `DRModel p` of the full modular function field at level $p$, with structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb Z$, the assertions that this morphism is proper and flat, that `DRModel p` is integral and has integrally closed sections on affine opens, curve models of the generic fibre over $\mathbb Q$ and over $\overline{\mathbb Q}$ together with isomorphisms onto the corresponding base changes and Galois- and place-compatibility conditions, two sections $\varepsilon_\infty$, $\varepsilon_0$ of `DRModel.toBase p` over the identity of $\operatorname{Spec}\mathbb Z$, an open subscheme `𝔛.smoothLocus` that is smooth of relative dimension $1$ over $\operatorname{Spec}\mathbb Z$ and contains every open on which the structure morphism is smooth, and further data including, for a field, the morphisms `𝔛.compInf` and `𝔛.compZero`. Let $k$ be an algebraically closed field of characteristic $p$, and let $y$ be a point of the topological space of the pullback $X_k$ of `DRModel.toBase p` along $\operatorname{Spec}$ of $\mathbb Z \to k$. Assume $y$ lies in the image of the continuous map underlying `𝔛.compInf k` and not in the image of the one underlying `𝔛.compZero k`. Then the image of $y$ under the first projection $X_k \to$ `DRModel p` lies in `𝔛.smoothLocus`, and $y$ lies in the connected component, formed inside the preimage of `𝔛.smoothLocus` under that projection, of the point obtained by evaluating at the closed point of $\operatorname{Spec} k$ the canonical section of $X_k \to \operatorname{Spec} k$ induced by $\varepsilon_\infty$ (namely the lift of $\operatorname{Spec}(\mathbb Z\to k)$ followed by $\varepsilon_\infty$ together with the identity).
--
--   This is the local form, at the level of the geometric fibre in characteristic $p$, of the Deligne–Rapoport description of the reduction of $X_0(p)$ as two components meeting transversally: away from the $0$-component the fibre is smooth and the $\infty$-component is connected and contains the reduction of the cusp section $\varepsilon_\infty$. It feeds the statements `iotaFin_mem_smoothLocus_of_aeval_mem` and `mem_connectedComponentIn_of_aeval_mem`, which identify concrete points of the fibre lying in the smooth locus and in the cusp component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve AlgebraicGeometry.RelPicard

theorem ModularCurve.DRModelPackage.mem_smoothLocus_and_mem_connectedComponentIn_of_mem_range_compInf
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
    (hy : y ∈ Set.range (𝔛.compInf k).base) (hy' : y ∉ Set.range (𝔛.compZero k).base) :
    (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ 𝔛.smoothLocus ∧
      y ∈ connectedComponentIn
        ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus :
            (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) :
          Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
        (((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k)) := by sorry
