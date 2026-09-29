-- Prove2me | Theorems.Thm_ModularCurve_ord_jBar_sub_1728_dvd_two_of_odd
-- name    : ModularCurve.ord_jBar_sub_1728_dvd_two_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/943e91b2-5da7-5b9b-971f-169e45a09520
-- title:
--   Ramification over j=1728 divides 2 for odd level
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and $N$ odd. Write $\overline{\mathbb{Q}}$ for `AlgebraicClosure ℚ` and let `modularFunctionFieldBar N` be the intermediate field of $\overline{\mathbb{Q}} \subseteq \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ obtained by adjoining to $\overline{\mathbb{Q}}$ the image, under the coefficientwise embedding $\mathrm{LaurentSeries}(\mathbb{Q}) \to \mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ induced by $\mathbb{Q} \to \overline{\mathbb{Q}}$, of `modularFunctionFieldFull N`, itself the subfield of $\mathrm{LaurentSeries}(\mathbb{Q})$ generated over $\mathbb{Q}$ by the family `divisorExpansions N`. Let `jBar N` be the element of this field given by the coefficientwise image of the $q$-expansion `jq` of the modular invariant. Let $v$ be a place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$, that is, a valuation subring of it which is not the whole field, contains the image of $\overline{\mathbb{Q}}$, and is a principal ideal ring; for an element $f$, $v.\mathrm{ord}(f)$ is minus the logarithm of the value of $f$ under the associated adic valuation. Assume $v.\mathrm{ord}(\bar\jmath - 1728) > 0$, where $1728$ is the image of $1728 \in \overline{\mathbb{Q}}$. Then $v.\mathrm{ord}(\bar\jmath - 1728)$ divides $2$ in $\mathbb{Z}$.
--
--   This is the classical bound on the ramification of $X_0(N) \to X(1)$ over the elliptic point $j = 1728$, whose isotropy in $\mathrm{PSL}_2(\mathbb{Z})$ has order $2$, in the form of a divisibility for the order of vanishing of $\bar\jmath - 1728$ at a place, valid for odd level. It feeds the count of places in the fibre over $1728$ used in [`ModularCurve.two_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar_sub_1728`](thm.html#ModularCurve.two_mul_card_eq_dedekindPsi_add_of_forall_mem_iff_pos_ord_jBar_sub_1728) and thence in the genus computation for `modularFunctionFieldBar` at prime level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jBar_sub_1728_dvd_two_of_odd.lean

import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.ord_jBar_sub_1728_dvd_two_of_odd (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hpos : 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728)) :
    v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ∣ 2 := by sorry
