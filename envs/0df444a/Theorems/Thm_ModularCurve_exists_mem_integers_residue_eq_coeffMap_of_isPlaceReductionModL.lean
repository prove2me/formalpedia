-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
-- name    : ModularCurve.exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/77a6fd72-7f02-521c-a77c-68aa4129da76
-- title:
--   q-expansion principle for constant reductions of X₀(N)
-- statement:
--   Fix $N \ge 1$ and a prime $p$ with $p \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, and write $k = \mathrm{ResidueField}\,A$. Let $F =$ `modularFunctionFieldBar N`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the elements of `modularFunctionFieldFull N` $\subseteq \mathbb Q((q))$, the latter being generated over $\mathbb Q$ by the $q$-expansions $j(q^d)$ for the divisors $d$ of $N$; and let $\bar F =$ `modularFunctionFieldFullC k N`, generated over $k$ by the series $\mathrm{qExpand}\,k\,d\,(\mathrm{jqModC}\,k)$ for $d \mid N$. Let $R$ be a `ConstantReduction` of $A$ from $F$ to $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ meeting the constants exactly in $A$, a surjective residue homomorphism onto $\bar F$ with kernel the maximal ideal and compatible with $A \to k$ on constants, such that every nonzero $f \in F$ has a constant multiple lying in $R.\mathrm{integers}$ with nonzero residue, together with a degree-preserving map $R.\mathrm{placeMap}$ on places carrying the divisor of any element of $R.\mathrm{integers}$ with nonzero residue to the divisor of that residue. Assume `IsPlaceReductionModL`: $R.\mathrm{placeMap}$ preserves degrees and, for every Laurent series $y$ over $A$ whose coefficientwise image lies in $F$ and whose coefficientwise reduction lies in $\bar F$ and is nonzero, the pushforward along $R.\mathrm{placeMap}$ of the divisor of the former equals the divisor of the latter. Then for every Laurent series $y$ over $A$ whose coefficientwise image $g$ lies in $F$, the element $g$ belongs to $R.\mathrm{integers}$ and its residue, regarded inside $k((q))$, is the coefficientwise reduction of $y$ along $A \to k$.
--
--   This is the $q$-expansion principle for constant reductions of the modular function field of level $N$ at a prime of residue characteristic prime to $N$: $q$-integral modular functions are integral for the reduction, and their residues are computed coefficientwise on $q$-expansions. No hypothesis on the genus or on the quality of the reduction enters; the result is used in the construction of uniformly adapted bases ([`ModularCurve.exists_uniform_adapted_basis`](thm.html#ModularCurve.exists_uniform_adapted_basis)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL.lean

import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_mem_integers_residue_eq_coeffMap_of_isPlaceReductionModL
    (N : ℕ) [NeZero N] {p : ℕ} [Fact p.Prime] (hpN : ¬ p ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (R : ConstantReduction A (modularFunctionFieldBar N)
        (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))
    (hR : IsPlaceReductionModL A N R.placeMap)
    (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N) :
    ∃ hmem : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
      ((R.residue ⟨_, hmem⟩ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        coeffMap (IsLocalRing.residue A) y := by sorry
