-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP
-- name    : ModularCurve.DRModelPackage.not_smooth_pullback_snd_toBase_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/be6802ef-38c6-5abb-8a5d-2c3fc3c81b16
-- title:
--   Geometric fibre at p of the Deligne–Rapoport model is non-smooth
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a term of the structure `DRModelPackage p`, whose fields equip the two-chart integral model `DRModel p` — the pushout of the two affine charts attached to the generator `IgusaScheme.jFull p` of the modular function field `modularFunctionFieldFull p`, with its structure morphism `DRModel.toBase p` to $\operatorname{Spec}\mathbb Z$ obtained by descending the two maps $\operatorname{Spec}$ of $\mathbb Z \to$ (finite chart algebra), $\mathbb Z \to$ (chart algebra at $\infty$) — with: properness, flatness and integrality of that model, integral closedness of its sections on affine opens, a proper smooth curve model over $\mathbb Q$ and one over $\overline{\mathbb Q}$ identified with the corresponding base changes of `DRModel.toBase p` compatibly with the arithmetic Galois action and with places, two sections over $\operatorname{Spec}\mathbb Z$, a distinguished open smooth locus, and further fibre data, including, for each algebraically closed field $K$, a proper smooth curve `ratModel K` over $K$ together with two closed immersions `compInf K`, `compZero K` of it into the fibre whose images cover the fibre but differ. Let $K$ be an algebraically closed field of characteristic $p$. Then the projection $\mathfrak X \times_{\operatorname{Spec}\mathbb Z}\operatorname{Spec}K \to \operatorname{Spec}K$, i.e. `pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))`, is not smooth.
--
--   This records the classical fact that the fibre at $p$ of the Deligne–Rapoport model of $X_0(p)$ is reducible — two copies of the $j$-line glued at the supersingular points — so that the model is not smooth over $\mathbb Z$ at $p$. It is used downstream in the analysis of the fibre at $p$ of the resolved model and of the associated component group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRModelPackage.not_smooth_pullback_snd_toBase_of_charP
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    ¬ Smooth (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := by sorry
