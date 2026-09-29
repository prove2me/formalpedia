-- Prove2me | Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
-- name    : ModularCurve.pow_mem_ssJSet_iff_of_perfectField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/5d33e79c-e7c7-582e-8dbc-55767e09a0f2
-- title:
--   Frobenius invariance of the supersingular j-set
-- statement:
--   Let $K$ be a field equipped with decidable equality, let $q$ be a natural number that is prime, assume $K$ has characteristic $q$ and is perfect, and let $a \in K$. Here [`ModularCurve.ssJSet q K`](def/ModularCurve_SupersingularModuli.html#L7) denotes the set of those $j \in K$ with the property that for every Weierstrass curve $W$ over $K$ which is elliptic (i.e. carries the `IsElliptic` instance) and satisfies $W.j = j$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is already the zero point; that is, the $K$-rational $q$-torsion of every elliptic curve over $K$ with $j$-invariant $j$ is trivial. The theorem asserts the equivalence $$a^{q} \in \mathrm{ssJSet}(q,K) \iff a \in \mathrm{ssJSet}(q,K),$$ so membership in this set is unchanged by raising to the $q$-th power, and (by perfectness) by extracting $q$-th roots. No further hypothesis on $a$ or on $K$ is imposed.
--
--   This is the statement that the condition defining the set of $j$-invariants with trivial $K$-rational $q$-torsion is stable under the Frobenius automorphism of a perfect field of characteristic $q$; classically it reflects the fact that supersingularity is invariant under isomorphism and under field automorphisms. It is used throughout the study of supersingular moduli in the project, for instance in the analysis of the Igusa scheme and of component charts on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField.lean

import Mathlib.FieldTheory.Perfect
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.pow_mem_ssJSet_iff_of_perfectField {K : Type*} [Field K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    a ^ q ∈ ModularCurve.ssJSet q K ↔ a ∈ ModularCurve.ssJSet q K := by sorry
