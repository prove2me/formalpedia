-- Prove2me | Theorems.Thm_ModularCurve_finite_cycSub
-- name    : ModularCurve.finite_cycSub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/302f0eb2-7bf8-57ad-a76f-8404e468e290
-- title:
--   Finitely many cyclic subgroups of order N on an elliptic curve over ℚ̄
-- statement:
--   Let $N$ be a natural number that is nonzero, and let $E_0$ be a Weierstrass curve over an algebraic closure of $\mathbb{Q}$ which is elliptic (its discriminant is a unit). Write $E_0^{\mathrm{aff}}$ for the associated affine curve and $E_0^{\mathrm{aff}}(\overline{\mathbb{Q}})$ for its group of points, in the sense of `WeierstrassCurve.Affine.Point`. The type `CycSub E₀ N` is defined as the subtype consisting of those additive subgroups $H$ of $E_0^{\mathrm{aff}}(\overline{\mathbb{Q}})$ for which there exists a point $g$ whose additive order is exactly $N$ and such that $H$ is the subgroup $\mathbb{Z}g$ of integer multiples of $g$; thus its elements are the cyclic subgroups of order exactly $N$, each recorded together with the existence of a generator of order $N$. The assertion is that this type is finite, i.e. there are only finitely many such subgroups.
--
--   This is the finiteness of the set of cyclic subgroups of order $N$ on a fixed elliptic curve over $\overline{\mathbb{Q}}$, the finiteness underlying the fact that a point of the modular curve of level $N$ has only finitely many level structures above a given $j$-invariant. It is used in the counting of elliptic points, in [`ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.card_filter_ord_jBar_eq_one_eq_nuThree) and [`ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.card_filter_ord_jBar_sub_1728_eq_one_eq_nuTwo), and in [`ModularCurve.emd_holds`](thm.html#ModularCurve.emd_holds).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finite_cycSub.lean

import Definitions.Def_ModularCurve_EMD

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.finite_cycSub (N : ℕ) [NeZero N] (E₀ : WeierstrassCurve (AlgebraicClosure ℚ)) [E₀.IsElliptic] :
    Finite (CycSub E₀ N) := by sorry
