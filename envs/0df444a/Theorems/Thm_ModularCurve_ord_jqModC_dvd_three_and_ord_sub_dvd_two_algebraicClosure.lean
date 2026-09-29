-- Prove2me | Theorems.Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_algebraicClosure
-- name    : ModularCurve.ord_jqModC_dvd_three_and_ord_sub_dvd_two_algebraicClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/51295a0a-2516-55d4-a929-2d95267e7147
-- title:
--   Ramification over j=0 and j=1728 divides 3 and 2
-- statement:
--   Fix $N\ge 1$ (non-zero) and write $\bar{\mathbb Q}$ for `AlgebraicClosure ℚ`. Let $F=$ `modularFunctionFieldFullC` $\bar{\mathbb Q}\,N$ be the intermediate field of $\bar{\mathbb Q}((q))=$ `LaurentSeries` $\bar{\mathbb Q}$ obtained by adjoining to $\bar{\mathbb Q}$ the set of series $qExpand\,\bar{\mathbb Q}\,d\,(jqModC\,\bar{\mathbb Q})$ for the non-zero divisors $d$ of $N$, where `jqModC` $K$ is the Laurent series $q^{-1}\cdot (E_4^3\,\eta^{-24})$, the $q$-expansion of the modular invariant $j$ with its integer coefficients mapped into $K$. Let $j\in F$ denote `jqModC` $\bar{\mathbb Q}$ together with its membership in $F$ (the case $d=1$). Let $w$ be any place of $F$ over $\bar{\mathbb Q}$, that is, a valuation subring of $F$ that contains the image of $\bar{\mathbb Q}$, is not all of $F$, and is a principal ideal ring; its $\operatorname{ord}$ is minus the logarithm of the associated height-one-spectrum adic valuation, an integer. The assertion is twofold: if $\operatorname{ord}_w(j)>0$ then $\operatorname{ord}_w(j)$ divides $3$, and if $\operatorname{ord}_w(j-1728)>0$, where $1728$ is taken in $F$ through the structure map from $\bar{\mathbb Q}$, then $\operatorname{ord}_w(j-1728)$ divides $2$.
--
--   This is the statement that the covering of modular curves of level $N$ over $\bar{\mathbb Q}$ ramifies over the elliptic points $j=0$ and $j=1728$ only to orders dividing $3$ and $2$ respectively, the orders of the stabilisers of $\rho$ and $i$ in $\mathrm{PSL}_2(\mathbb Z)$, recorded here for the function field presented as a subfield of $\bar{\mathbb Q}((q))$. It supplies the ramification hypothesis used in the degree and dimension computations for modular forms, and is cited in [`ModularCurve.exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card`](thm.html#ModularCurve.exists_linearIndependent_isModPFormFn_algebraicClosure_dimFormula_le_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jqModC_dvd_three_and_ord_sub_dvd_two_algebraicClosure.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

theorem ModularCurve.ord_jqModC_dvd_three_and_ord_sub_dvd_two_algebraicClosure (N : ℕ) [NeZero N] :
    ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N),
      (0 < w.ord (⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) N⟩ : ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N)) →
          w.ord (⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) N⟩ : ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N)) ∣ 3) ∧
      (0 < w.ord ((⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) N⟩ : ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N)) - algebraMap (AlgebraicClosure ℚ) _ 1728) →
          w.ord ((⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_full (AlgebraicClosure ℚ) N⟩ : ↥(modularFunctionFieldFullC (AlgebraicClosure ℚ) N)) - algebraMap (AlgebraicClosure ℚ) _ 1728) ∣ 2) := by sorry
