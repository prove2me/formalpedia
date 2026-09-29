-- Prove2me | Theorems.Thm_ModularCurve_restrict_eq_jLinePlace1728_iff
-- name    : ModularCurve.restrict_eq_jLinePlace1728_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8eaea59a-aa6c-59cc-a353-a8520358efe3
-- title:
--   A place of the modular function field restricts to j=1728 iff ord_w(j-1728)>0
-- statement:
--   Fix $N \ge 1$ and work inside the Laurent series field $\mathrm{LaurentSeries}\,\mathbb{Q}$, with [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) the $q$-expansion of the $j$-invariant and [`ModularCurve.modularFunctionField N`](def/ModularCurve_X0.html#L250) the intermediate field $\mathbb{Q}(\mathtt{jq}, \mathtt{qExpand}\ N\ \mathtt{jq})$ generated over $\mathbb{Q}$ by `jq` and by its image under the $N$-fold rescaling of the exponent; it is an algebra over the subfield $\mathbb{Q}\langle \mathtt{jq}\rangle$ via the inclusion [`ModularCurve.jAdjoinRingHom`](def/ModularCurve_RouteBCoordRing.html#L14). Assume this extension is integral, and let $w$ be a place of `modularFunctionField N` over $\mathbb{Q}$, i.e. a valuation subring containing the image of $\mathbb{Q}$, distinct from the whole field and a principal ideal ring. Its restriction $w|_{\mathbb{Q}\langle \mathtt{jq}\rangle}$ is the pullback valuation subring along the inclusion. The assertion is that this restriction equals [`ModularCurve.jLinePlace1728`](def/ModularCurve_JLinePlaces.html#L50) — the place of $\mathbb{Q}\langle \mathtt{jq}\rangle$ obtained by transporting, along the isomorphism $\mathrm{RatFunc}\,\mathbb{Q} \cong \mathbb{Q}\langle \mathtt{jq}\rangle$ coming from the transcendence of `jq`, the finite place of $\mathrm{RatFunc}\,\mathbb{Q}$ attached to $X - 1728$ — precisely when $\mathrm{ord}_w(\mathtt{jq} - 1728) > 0$, where $\mathrm{ord}_w$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation and `jq` is viewed in `modularFunctionField N`.
--
--   This is the criterion identifying the places of the function field of $X_0(N)$ that lie over the elliptic point $j = 1728$ of the $j$-line, expressed through vanishing of $j - 1728$. It is used in the counts of fibres over $j = 0$ and $j = 1728$, namely in [`ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree`](thm.html#ModularCurve.natCard_ord_jBar_eq_one_eq_nuThree) and [`ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo`](thm.html#ModularCurve.natCard_ord_jBar_sub_1728_eq_one_eq_nuTwo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_restrict_eq_jLinePlace1728_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_JLinePlaces
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IntermediateField AlgebraicCurve

theorem ModularCurve.restrict_eq_jLinePlace1728_iff (N : ℕ) [NeZero N] :
    letI := ModularCurve.jAdjoinAlgebra N
    ∀ [Algebra.IsIntegral ↥ℚ⟮ModularCurve.jq⟯ ↥(ModularCurve.modularFunctionField N)]
      (w : AlgebraicCurve.Place ℚ ↥(ModularCurve.modularFunctionField N)),
      w.restrict ↥ℚ⟮ModularCurve.jq⟯ = ModularCurve.jLinePlace1728 ↔
        0 < w.ord ((⟨ModularCurve.jq, ModularCurve.jq_mem N⟩ : ↥(ModularCurve.modularFunctionField N)) - 1728) := by sorry
