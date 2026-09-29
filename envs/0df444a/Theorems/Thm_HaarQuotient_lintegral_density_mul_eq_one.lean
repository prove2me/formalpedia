-- Prove2me | Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
-- name    : HaarQuotient.lintegral_density_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/e3b0e80f-c457-5c07-b3ae-e92d528d06a5
-- title:
--   Bruhat density integrates to one over each coset
-- statement:
--   Let $G$ be a group carrying a topology making it a topological group, locally compact and second countable, equipped with its Borel $\sigma$-algebra (the standard measurability typeclasses being assumed), let $H \le G$ be a subgroup whose underlying set is closed in $G$, and let $\mu_H$ be a measure on $H$ that is a Haar measure and is in addition right invariant, so that $H$ is unimodular. Write $w =$ [`HaarQuotient.weight H μH`](def/HaarQuotient.html#L12) for the function $G \to [0,\infty]$ which, when $G$ is $\sigma$-compact and weakly locally compact (as it is here), is given in terms of a fixed compact exhaustion $E_0 \subseteq E_1 \subseteq \cdots$ of $G$ by $$w(g) \;=\; \sum_{n \ge 0} 2^{-n}\,\bigl(1 + \mu_H\bigl(\{x \in H : x \in E_{n+1}E_{n+1}^{-1}\}\bigr)\bigr)^{-1}\,\mathbf 1_{\operatorname{int} E_{n+1}}(g),$$ and is $0$ otherwise, and write $\delta(g) =$ [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25) $(g) = w(g) \big/ \int_H w(x g)\,d\mu_H(x)$, the quotient being taken in $[0,\infty]$. The assertion is that for every $g \in G$ the lower Lebesgue integral of $x \mapsto \delta(xg)$ over $H$ against $\mu_H$ equals $1$.
--
--   This is the normalisation property of a Bruhat function: the weight $w$ is renormalised coset by coset so that the resulting density has total mass one on every right coset $Hg$, which is what allows a quotient measure on $H \backslash G$ to be built by unfolding integrals. It is used throughout the construction and comparison of invariant measures on adelic quotients, for instance in the Iwasawa-type decompositions of integrals over unipotent and torus quotients appearing in the automorphic part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HaarQuotient_lintegral_density_mul_eq_one.lean

import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem HaarQuotient.lintegral_density_mul_eq_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (g : G) :
    ∫⁻ x : H, HaarQuotient.density H μH ((x : G) * g) ∂μH = 1 := by sorry
