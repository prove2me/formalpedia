-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed
-- name    : ModularCurve.XHDRModelAtP.isReduced_pullback_toBase_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/225ed62f-6665-51d4-9f26-b3b53cd3cc5a
-- title:
--   Geometric fibres of the X_H(M) model at p are reduced
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a divisibility $p \mid M$. Let $hj$ record that the Laurent series $j_q = q^{-1}\cdot(\text{the integral power series } jNum)$ over $\mathbb{Q}$ lies in $qExpFunctionFieldC\ \mathbb{Q}\ \top$, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions of the ratios of integral forms for $\mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be an inhabitant of the structure `XHDRModelAtP p M H hpM hj`, which packages: properness, flatness, local finite presentation and integrality for the two-chart integral model $X$ at level $\Gamma_H(M)$ over $\mathrm{Spec}\,R_p$ together with normality of its affine sections; properness and relative-dimension-one smoothness at the auxiliary level $\Gamma_N$; a `CurveModel` over $\overline{\mathbb{Q}}$ with function field $xHFunctionFieldBar\ M\ H$ identified, Galois-equivariantly and compatibly with the chart coordinates, with the base change of the model to $\overline{\mathbb{Q}}$; smoothness of relative dimension one and geometric integrality of the generic fibre; and further data summarised in that structure, among them reducedness of the fibres over residue fields of places of $\overline{\mathbb{Q}}$ above $p$. Then for every algebraically closed field $k$ and every morphism $x : \mathrm{Spec}\,k \to \mathrm{Spec}\,R_p$, the scheme obtained by pulling back the structure morphism $toBase\ p\ (\Gamma_H(M))\ hj : X \to \mathrm{Spec}\,R_p$ along $x$ is reduced.
--
--   This is the statement that every geometric fibre of the Deligne–Rapoport model of $X_H(M)$ over $\mathbb{Z}_{(p)}$, for $p \mid M$, is reduced, including the special fibre at $p$. It is used downstream in the analysis of the local structure of that model, for instance in the identification of branch ideals at the supersingular points and in the description of sections after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isReduced_pullback_toBase_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.isReduced_pullback_toBase_of_isAlgClosed
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (XHDRLevel.R p))) :
    IsReduced (pullback (XHDRLevel.toBase p (XHDRLevel.ΓM M H) hj) x) := by sorry
