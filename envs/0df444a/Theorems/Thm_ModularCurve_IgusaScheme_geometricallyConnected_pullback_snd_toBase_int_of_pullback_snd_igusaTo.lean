-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
-- name    : ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/d3888abd-1e71-533c-a6b1-702d5ccbcf85
-- title:
--   Geometric connectedness passes from the Igusa scheme to the ℤ-model
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$, let $k$ be a commutative ring, and let $\varphi$ be a ring homomorphism from $\mathbb{Z}_{(\ell)}$, realised as the subring [`GaloisRep.ratLocalizedAt`](def/GaloisRep_Flat.html#L8) $\ell$ of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$, to $k$. Write $F =$ `modularFunctionFieldFull` $N$ for the subfield of the field of Laurent series over $\mathbb{Q}$ generated over $\mathbb{Q}$ by the $q$-expansions `qExpand ℚ d jq` for the nonzero divisors $d$ of $N$, and `jFull` $N$ for the element $j$ of $F$. The hypothesis is that the second projection of the pullback of `igusaTo` $N$ $\ell$ — the structure morphism to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ of the scheme obtained by glueing $\operatorname{Spec}$ of the $\mathbb{Z}_{(\ell)}$-subalgebra of $F$ attached to $\{j\}$ and $\operatorname{Spec}$ of the one attached to $\{j^{-1}\}$ along the middle chart — along $\operatorname{Spec} \varphi$ is geometrically connected as a morphism of schemes. The conclusion is that the second projection of the pullback of [`AlgebraicCurve.TwoChartIntegralModel.toBase`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) for the data $(\mathbb{Z}, F, j)$, i.e. the structure morphism to $\operatorname{Spec} \mathbb{Z}$ of the analogous two-chart model formed over $\mathbb{Z}$, along $\operatorname{Spec}$ of the canonical map $\mathbb{Z} \to k$, is geometrically connected.
--
--   The statement transfers geometric connectedness of a fibre of the Igusa model of the modular curve over $\mathbb{Z}_{(\ell)}$ to the corresponding fibre of the two-chart integral model over $\mathbb{Z}$, for any ring $k$ receiving $\mathbb{Z}_{(\ell)}$; it is the local-to-global step used by [`ModularCurve.IgusaScheme.geometricallyConnected_toBase_int`](thm.html#ModularCurve.IgusaScheme.geometricallyConnected_toBase_int), where connectedness of the fibres of the $\mathbb{Z}$-model is established prime by prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_toBase_int_of_pullback_snd_igusaTo
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (k : Type) [CommRing k]
    (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (h : GeometricallyConnected (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ)))) :
    GeometricallyConnected
      (pullback.snd
        (AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull N) (jFull N))
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by sorry
