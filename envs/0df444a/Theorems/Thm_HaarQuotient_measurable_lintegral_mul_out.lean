-- Prove2me | Theorems.Thm_HaarQuotient_measurable_lintegral_mul_out
-- name    : HaarQuotient.measurable_lintegral_mul_out
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/eaf1e7e6-fa02-57a4-993a-9d86dcd573f5
-- title:
--   Measurability of orbit integrals on the coset space H backslash G
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, locally compact and second countable, equipped with its Borel $\sigma$-algebra (a measurable space structure assumed to be the Borel structure of the topology). Let $H$ be a subgroup of $G$ whose underlying set is closed in $G$, and let $\mu_H$ be a measure on the subtype $H$ which is a Haar measure (hence left invariant, with the usual regularity and positivity-on-open-sets conditions) and is moreover right invariant. Let $f \colon G \to [0,\infty]$ be measurable, with values in the extended non-negative reals. The assertion is that the function on the orbit space `MulAction.orbitRel.Quotient H G` of the left multiplication action of $H$ on $G$, that is on the space $H \backslash G$ of right cosets, sending a class $q$ to the lower Lebesgue integral $\int_H f(x \cdot q_{\mathrm{out}}) \, d\mu_H(x)$, where $x$ runs over $H$ viewed inside $G$ and $q_{\mathrm{out}} \in G$ is the representative of $q$ produced by the choice function `Quotient.out`, is measurable for the $\sigma$-algebra coinduced on the quotient along the projection, i.e. the one whose measurable sets are those with Borel preimage in $G$.
--
--   This is the measurability half of the classical integration formula for the quotient of a locally compact group by a closed unimodular subgroup: right invariance of $\mu_H$ makes the orbit integral independent of the chosen representative, so the displayed function is the descent to $H \backslash G$ of $g \mapsto \int_H f(xg)\,d\mu_H(x)$. It is used in the adelic analysis on $\mathrm{GL}$, where integrals over the adelic group are unfolded into integrals over the quotient by the global points and sums over that discrete group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_measurable_lintegral_mul_out.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem HaarQuotient.measurable_lintegral_mul_out
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH := by sorry
