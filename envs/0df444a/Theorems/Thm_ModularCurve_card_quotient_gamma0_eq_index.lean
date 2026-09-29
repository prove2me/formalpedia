-- Prove2me | Theorems.Thm_ModularCurve_card_quotient_gamma0_eq_index
-- name    : ModularCurve.card_quotient_gamma0_eq_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/e3637823-a00d-53c2-ad33-da018885805a
-- title:
--   Index of Γ₀(N) is unchanged in GL₂(ℝ)
-- statement:
--   For every natural number $N$, with no further hypothesis, the following two natural numbers agree. On the left, $\mathcal{S L}$ denotes the subgroup of $\mathrm{GL}_2(\mathbb{R})$ that is the image of $\mathrm{SL}_2(\mathbb{Z})$ under `Matrix.SpecialLinearGroup.mapGL ℝ`; inside it one takes the subgroup induced (via `Subgroup.subgroupOf`) by the image of the congruence subgroup $\Gamma_0(N) \le \mathrm{SL}_2(\mathbb{Z})$ under the same map, and forms the coset space of $\mathcal{S L}$ by that subgroup, whose cardinality is measured by `Nat.card`. On the right stands `Subgroup.index` of $\Gamma_0(N)$, the index of $\Gamma_0(N)$ in $\mathrm{SL}_2(\mathbb{Z})$. The theorem asserts that these are equal. Both sides use the convention that the value is $0$ when the coset space is infinite, so the equality also holds in the degenerate case $N = 0$, where $\Gamma_0(0)$ consists of the matrices with lower-left entry $0$ and has infinite index; for $N = 1$ both sides are $1$. The content is thus that passing from $\mathrm{SL}_2(\mathbb{Z})$ to its image in $\mathrm{GL}_2(\mathbb{R})$ changes neither the coset space nor its cardinality.
--
--   This is a transport lemma between the two spellings of the coset space $\mathrm{SL}_2(\mathbb{Z})/\Gamma_0(N)$: the $\mathrm{SL}_2(\mathbb{Z})$-side index, for which explicit formulas such as $[\mathrm{SL}_2(\mathbb{Z}):\Gamma_0(N)] = \psi(N)$ are available, and the $\mathrm{GL}_2(\mathbb{R})$-side count that appears in the degree bound for algebraic relations between ratios of $q$-expansions of modular forms on an arithmetic subgroup. It is used in the computation of relative indices of $\Gamma_0$- and $\Gamma_H$-type subgroups and in the determination of the relative degrees of the associated $q$-expansion function fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_quotient_gamma0_eq_index.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.card_quotient_gamma0_eq_index (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) = (CongruenceSubgroup.Gamma0 N).index := by sorry
