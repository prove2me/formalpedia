-- Prove2me | Theorems.Thm_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
-- name    : ModularCurve.residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/1cdfc2da-60cd-5727-9701-e8e1c0bc1ab1
-- title:
--   Ogg's unit reduces to the supersingular polynomial
-- statement:
--   Fix natural numbers $N \ge 1$ and a prime $p$ with $5 \le p$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a nonunit of $A$; write $k =$ `IsLocalRing.ResidueField A`. Assume that Ogg's series [`ModularCurve.modularUnitSeries p`](def/ModularCurve_ModularUnit.html#L127) $= \Delta(\mathfrak q)\,\Delta(\mathfrak q^p)^{-1}$, formed from $\Delta(\mathfrak q) = \mathfrak q \cdot \eta\text{-unit}$ and its $p$-fold $\mathfrak q$-expansion substitute, lies in `modularFunctionFieldFull (N * p)`, the subfield of $\mathbb Q((\mathfrak q))$ generated over $\mathbb Q$ by the divisor expansions of level $Np$. Let $R_0$ be a regular prolongation of $A$ to $F =$ `modularFunctionFieldBar (N * p)` (the field generated over $\overline{\mathbb Q}$ inside $\overline{\mathbb Q}((\mathfrak q))$ by the coefficientwise images of that level-$Np$ field) with residue field `modularFunctionFieldFullC k N` (generated over $k$ inside $k((\mathfrak q))$ by the level-$N$ divisor expansions): that is, a valuation subring $R_0.\mathrm{integers}$ of $F$ together with a surjective ring homomorphism $\mathrm{res}$ onto that residue field whose kernel is the maximal ideal, compatible with $A$ and its residue map, and satisfying the scaling condition. Assume further ($h_0$) that $\mathrm{res}$ is coefficientwise reduction: every $y \in A((\mathfrak q))$ whose image in $\overline{\mathbb Q}((\mathfrak q))$ lies in $F$ is $R_0$-integral, with residue the Laurent series obtained by applying $A \to k$ to the coefficients of $y$. Finally let $S_0$ be a finite subset of $k$ whose members are exactly the elements of `ssJSet p k`, i.e. those $j \in k$ such that every elliptic curve over $k$ with $j$-invariant $j$ has no nonzero $p$-torsion point. Then the element $u \in F$ obtained from `modularUnitSeries p` by coefficientwise embedding $\mathbb Q \hookrightarrow \overline{\mathbb Q}$ satisfies: $u$ and $u^{-1}$ both lie in $R_0.\mathrm{integers}$, and the Laurent series over $k$ underlying $\mathrm{res}(u)$ equals $\prod_{a \in S_0} (\bar\jmath - a)^{12 / e(a)}$, where $\bar\jmath =$ `jqModC k` is the $\mathfrak q$-expansion of $j$ with coefficients reduced into $k$, $e(a) =$ `jWidth a` is $3$ for $a = 0$, $2$ for $a = 1728$ and $1$ otherwise, and the exponent is the natural-number quotient $12/e(a)$.
--
--   This identifies the restriction of Ogg's modular unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^p)$ to the component of the cusp $\infty$ in the characteristic-$p$ fibre of $X_0(Np)$ with the weighted supersingular polynomial in $j$, a polynomial of degree $p-1$ vanishing exactly at the supersingular $j$-invariants with multiplicity $12/e(a)$. It feeds [`ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet`](thm.html#ModularCurve.exists_laurentSeries_int_modularUnitSeries_coeffMap_eq_prod_ssJSet), part of the analysis of the special fibre of $X_0(Np)$ used in level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation.lean

import Mathlib
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in

theorem ModularCurve.residue_coeffEmb_modularUnitSeries_eq_prod_ssJSet_of_regularProlongation
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hp : 5 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (hmem : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (N * p))
    (R₀ : AlgebraicCurve.RegularProlongation A (ModularCurve.modularFunctionFieldBar (N * p))
      (ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N))

    (h₀ : ∀ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.modularFunctionFieldBar (N * p)),
      ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
        (((R₀.residue ⟨_, hint⟩ :
            ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
            LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.coeffMap (IsLocalRing.residue A) y)
    [DecidableEq (IsLocalRing.ResidueField A)] (S₀ : Finset (IsLocalRing.ResidueField A))
    (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ModularCurve.ssJSet p (IsLocalRing.ResidueField A)) :
    ∃ hu₀ : (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p)) ∈ R₀.integers,
      (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.modularUnitSeries p),
          ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ :
          ModularCurve.modularFunctionFieldBar (N * p))⁻¹ ∈ R₀.integers ∧
      (((R₀.residue ⟨_, hu₀⟩ :
          ModularCurve.modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) :
          LaurentSeries (IsLocalRing.ResidueField A)) =
        ∏ a ∈ S₀, (ModularCurve.jqModC (IsLocalRing.ResidueField A) - HahnSeries.C a) ^
          (12 / ModularCurve.jWidth a) := by sorry
