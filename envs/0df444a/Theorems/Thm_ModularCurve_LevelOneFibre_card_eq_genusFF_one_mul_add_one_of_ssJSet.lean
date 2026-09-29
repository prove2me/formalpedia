-- Prove2me | Theorems.Thm_ModularCurve_LevelOneFibre_card_eq_genusFF_one_mul_add_one_of_ssJSet
-- name    : ModularCurve.LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/100f4815-12c1-5759-b123-c2239b492aba
-- title:
--   Supersingular j-invariant count equals genus of X₀(1· q) plus one
-- statement:
--   Let $q$ be a prime with $q \ge 5$, and let $k$ be an algebraically closed field of characteristic $q$. Let $S_0$ be a finite subset of $k$ whose members are exactly the elements of `ssJSet q k`, that is, those $j \in k$ such that for every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $j$, the only point $P$ of the associated affine curve with $q \cdot P = 0$ is $P = 0$ (the supersingular $j$-invariants, characterised by vanishing of $q$-torsion). The conclusion is that the cardinality of $S_0$ equals $g + 1$, where $g =$ `genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))` is the genus, defined as the $\overline{\mathbb{Q}}$-dimension of the space $H^1$ of the zero divisor, of the field $\overline{\mathbb{Q}}$-generated inside $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$ by the coefficientwise image of the level-$(1 \cdot q)$ modular function field, the latter being the subfield of $\mathrm{LaurentSeries}(\mathbb{Q})$ obtained by adjoining to $\mathbb{Q}$ the divisor expansions at level $1 \cdot q$. The level is written $1 \cdot q$ rather than $q$.
--
--   This is the Deuring–Eichler count of supersingular $j$-invariants in characteristic $q$, matched against the genus of $X_0(q)$ over $\overline{\mathbb{Q}}$; geometrically it records that the special fibre at $q$ of the Deligne–Rapoport model of $X_0(q)$ consists of two rational components crossing at the supersingular points. The form with the level spelled $1 \cdot q$ is the one consumed by the multiplicative-covering statements [`ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis`](thm.html#ModularCurve.MultCovering.eq_mAnnuli_add_one_of_isEmbBasis), [`ModularCurve.MultCovering.infChart_chartData_goodFamily`](thm.html#ModularCurve.MultCovering.infChart_chartData_goodFamily) and [`ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal`](thm.html#ModularCurve.MultCovering.infChart_residue_eq_ssPolyBar_mul_of_orthogonal), where the level appears as a product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelOneFibre_card_eq_genusFF_one_mul_add_one_of_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.LevelOneFibre.card_eq_genusFF_one_mul_add_one_of_ssJSet
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) :
    S₀.card = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) + 1 := by sorry
