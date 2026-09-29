-- Prove2me | Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
-- name    : ModularCurve.pow_mem_ssJSet_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/468dcc11-0850-58ce-8834-43b9bd30eb25
-- title:
--   Frobenius-stability of the supersingular j-set
-- statement:
--   Let $K$ be a field (in `Type`, with decidable equality) of characteristic $q$ for a prime $q$, and suppose $K$ is perfect; let $a \in K$. Here [`ModularCurve.ssJSet q K`](def/ModularCurve_SupersingularModuli.html#L7) is the set of those $j \in K$ with the property that for every Weierstrass curve $W$ over $K$ which is elliptic (nonvanishing discriminant, so that its $j$-invariant is defined) and satisfies $W.j = j$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is the point at infinity; that is, no elliptic curve over $K$ with $j$-invariant $j$ has a nontrivial $K$-rational $q$-torsion point. The theorem asserts that $a^q$ belongs to this set if and only if $a$ does. Note that the condition is a statement about all $K$-rational $q$-torsion of all models with the given $j$-invariant, not about supersingularity over an algebraic closure; the equivalence is an instance of invariance of the set under the $q$-power Frobenius automorphism of the perfect field $K$.
--
--   The set [`ModularCurve.ssJSet`](def/ModularCurve_SupersingularModuli.html#L7) plays the role of the locus of supersingular $j$-invariants in characteristic $q$, and this lemma records its stability under Frobenius, together with the resulting symmetry $a \leftrightarrow a^q$. It is used in the treatment of the supersingular points of the modular curve of level $q$, notably in the constructions attached to full level structures and to the specialisation data at a place above $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_mem_ssJSet_iff.lean

import Mathlib.FieldTheory.Perfect
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.pow_mem_ssJSet_iff {K : Type} [Field K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] [PerfectField K] (a : K) :
    a ^ q ∈ ModularCurve.ssJSet q K ↔ a ∈ ModularCurve.ssJSet q K := by sorry
