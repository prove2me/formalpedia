-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
-- name    : ModularCurve.MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/3bed50e5-8b28-5593-a8fa-7c6808d2d420
-- title:
--   Source lift of a supersingular j-value on the zero chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that the image of $p$ is a nonunit of $A$, with residue field $k =$ `IsLocalRing.ResidueField A` of characteristic $p$. Let $\Gamma$ be a chart context for the multiplicative covering at $p$ along $A$, i.e. a `ChartCtx p A`, which packages modular polynomial data for $p$ together with its Kronecker congruence, the integrality hypotheses `HeckeAlphaBarIntegral` and `HeckeBetaBarIntegral` for $(\overline{\mathbb{Q}}, 1, p)$, a place specialisation $P$ of $A$ along the residue map, a level-one prolongation pair $R$ for $P$, a set $S_1$ of places of $\overline{\mathbb{Q}}$-base-changed level-$1\cdot p$ modular function field, a finset `Wn` of places of the level-one function field over $k$ characterised as the supersingular places `ssPlaces p 1 k`, a proof that the set `ssJSet p k` is finite with exactly `mAnnuli p` elements, and a chart-first supply for $R$ and $S_1$. Let $a \in k$ lie in `ssJSet p k`, that is: every elliptic Weierstrass curve over $k$ with $j$-invariant $a$ has no nonzero point killed by $p$. Write $e =$ `edgeOf Γ a ha` for the index of $a$ under the chosen enumeration of `ssJSet p k` by `Fin (mAnnuli p)`. Then there exists $x_l \in A$ whose residue in $k$ is $a$ and such that, first, the element $j_F - x_l$ of the base-changed modular function field of level $1\cdot p$ — where $j_F$ is the $q$-expansion of $j$ viewed there, and $x_l$ is mapped in by the structure map from $\overline{\mathbb{Q}}$ — lies in the valuation subring `integers` of the chart `chart Γ (src p e)`, the source chart of the edge $e$, which by definition of `src` is the index-$1$ chart `zeroChart Γ`; and, second, the image of $j_F - x_l$ under the `residue` homomorphism of that chart has strictly positive order at the place `nodeSrc Γ e`, namely at the place of the line over $k$ attached to the point $(\mathrm{ssValue}\ \Gamma\ e)^p$, where the order of a place is $-\log$ of its adic valuation.
--
--   This is the source half of the "tie" data relating the two components of the special fibre of $X_0(p)$ at a supersingular point: a lift to $A$ of a supersingular $j$-invariant for which $j$ minus that constant is regular on the zero chart and vanishes at the corresponding node. It is used in the assembly of the uniform multiplicative covering statement [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_lift_jF_sub_mem_chart_src_integers_and_ord_nodeSrc_pos (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime p) [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ∃ xl : ↥A, IsLocalRing.residue ↥A xl = a ∧
      ∃ h : jF p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (xl : AlgebraicClosure ℚ)
          ∈ (chart Γ (src p (edgeOf Γ a ha))).integers,
        0 < (nodeSrc Γ (edgeOf Γ a ha)).ord
          ((chart Γ (src p (edgeOf Γ a ha))).residue ⟨_, h⟩) := by sorry
