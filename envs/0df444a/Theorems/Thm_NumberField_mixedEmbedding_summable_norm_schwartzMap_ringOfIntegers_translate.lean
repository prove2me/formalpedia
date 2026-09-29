-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate
-- name    : NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/c92d1b2b-11a2-5951-b981-79791d3d4499
-- title:
--   Summability of a translated Schwartz sum over 𝒪_F
-- statement:
--   Let $F$ be a field which is a number field, and let $\mathrm{mixedSpace}\,F$ denote its mixed archimedean space $\prod_{v \text{ real}} \mathbb{R} \times \prod_{v \text{ complex}} \mathbb{C}$, with $\mathrm{mixedEmbedding}\,F \colon F \to \mathrm{mixedSpace}\,F$ the associated embedding. Given a Schwartz function $g \in \mathcal{S}(\mathrm{mixedSpace}\,F, \mathbb{C})$ — an element of the Schwartz space of smooth, rapidly decreasing $\mathbb{C}$-valued functions on the mixed space — and a point $x \in \mathrm{mixedSpace}\,F$, the assertion is that the family indexed by the ring of integers $\mathcal{O}_F$ whose value at $a$ is the real number $\|g(x + \mathrm{mixedEmbedding}\,F(a))\|$ is summable, $a$ being regarded as an element of $F$ before applying the embedding. Equivalently, $\sum_{a \in \mathcal{O}_F} \|g(x + \sigma(a))\| < \infty$ for the mixed embedding $\sigma$, i.e. the translated lattice sum of $g$ over $\mathcal{O}_F$ converges absolutely, uniformly in no parameter being claimed here: the statement is for each fixed $g$ and $x$.
--
--   This is the archimedean half of the summability needed for adelic Poisson summation over a number field: the sum of a Schwartz function over a translate of the lattice $\sigma(\mathcal{O}_F)$ in the mixed space converges absolutely. It is used by [`NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet`](thm.html#NumberField.AdelicFourier.summable_comp_algebraMap_of_mem_pureTensorSet), where the summability of a pure tensor over the principal points of the adeles is reduced to such an archimedean lattice sum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.lean

import Definitions.Def_NumberField_AdelicFourier
import Mathlib.Algebra.Module.ZLattice.Summable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.mixedEmbedding
open scoped SchwartzMap Classical

noncomputable section

theorem NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by sorry
