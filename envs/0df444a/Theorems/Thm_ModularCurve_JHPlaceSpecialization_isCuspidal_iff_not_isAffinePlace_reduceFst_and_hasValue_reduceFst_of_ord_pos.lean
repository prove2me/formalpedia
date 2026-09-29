-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/ac15a2b6-e294-5c70-b03b-23e8ada8b030
-- title:
--   First reading of a place: cuspidality and j-values
-- statement:
--   Fix a prime $p$ and $M \geq 1$ with $p \mid M$, $p^2 \nmid M$ and $M/p \neq 0$, a subgroup $H \leq (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $p$, i.e. with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M$ for the base change of the $q$-expansion function field of $X_H(M)$ to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$, $F_{M/p}$ for the corresponding field for $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F$ for the fibre field $\kappa$-version attached to $\Gamma_N(p,M,H)$. Let `Psp` be a place-specialization packet `JHPlaceSpecialization p M H hpM A`, with underlying map $\mathrm{sp}$ from places of $F_{M/p}$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$, let $\alpha \colon F_{M/p} \to F_M$ be an integral $\overline{\mathbb{Q}}$-algebra map which is the identity on $q$-expansions, and put $r_1(V) = \mathrm{sp}(V|_\alpha)$, the restriction of $V$ along $\alpha$ followed by $\mathrm{sp}$. Let $x \in F_M$ and $\bar x \in \bar F$ be elements whose $q$-expansions are `jqModC` over $\overline{\mathbb{Q}}$ and over $\kappa$ respectively. Then for every place $V$ of $F_M$ over $\overline{\mathbb{Q}}$ three assertions hold. First, $V$ is cuspidal — meaning that for every $y \in F_M$ with $q$-expansion `jqModC` and every $a \in A$ one has $\operatorname{ord}_V(y - a) \leq 0$ — if and only if $r_1(V)$ is not an affine place, i.e. there is no pair consisting of an element of $\bar F$ with $q$-expansion `jqModC` over $\kappa$ and a scalar in $\kappa$ which is its value at $r_1(V)$. Second, for every $a \in A$ with $\operatorname{ord}_V(x - a) > 0$, the element $\bar x$ lies in the valuation subring of $r_1(V)$ and its residue there is the image of $a$ in $\kappa$. Third, conversely, whenever $\bar x$ has a value $b \in \kappa$ at $r_1(V)$ there is $a \in A$ reducing to $b$ with $\operatorname{ord}_V(x - a) > 0$. Here $\operatorname{ord}_V$ is the negative logarithm of the associated height-one-spectrum valuation.
--
--   This is the place-by-place dictionary for the $j$-coordinate along the first degeneracy embedding: it identifies the cusps of $X_H(M)$ over $\overline{\mathbb{Q}}$ with the non-affine places of the special fibre and matches $A$-integral values of $j$ with their reductions. It is used in the construction of the de Rham model of $X_H$ at $p$, in the analysis of vertical units and of places attached to a prolongation datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ↔
        ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V)) ∧
      (∀ a : ↥A, 0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) →
        (Psp.reduceFst α hα V).HasValue xb (IsLocalRing.residue ↥A a)) ∧
      (∀ b : ResidueField ↥A, (Psp.reduceFst α hα V).HasValue xb b →
        ∃ a : ↥A, IsLocalRing.residue ↥A a = b ∧
          0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) := by sorry
