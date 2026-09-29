-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_ord_sub_algebraMap_pos_residue_notMem_of_isAffinePlace_reduceFst
-- name    : ModularCurve.JHPlaceSpecialization.exists_ord_sub_algebraMap_pos_residue_notMem_of_isAffinePlace_reduceFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/06a3544b-226a-5b63-8ed3-94460a5616c7
-- title:
--   Lifting a good j-value along the first degeneracy map
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`LiesOverPrime`) whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\alpha$ be an integral $\overline{\mathbb{Q}}$-algebra map from the level-$(M/p)$ field $F_{M/p}$, for the image subgroup `infSubgroup p M H hpM`, into the level-$M$ field $F_M$ (both intermediate fields of $\overline{\mathbb{Q}}$-Laurent series), assumed to act as the identity on underlying Laurent series. Let $P_{\mathrm{sp}}$ be a `JHPlaceSpecialization` at $A$, let $x_j \in F_M$ and $\bar x \in \bar F$ have Laurent series equal to the $q$-expansion `jqModC` over $\overline{\mathbb{Q}}$ and over $\kappa$ respectively, let $S \subseteq \kappa$ be finite, and let $V$ be a place of $F_M$ over $\overline{\mathbb{Q}}$. Assume its first reading $P_{\mathrm{sp}}.\mathrm{sp}(V|_\alpha)$ is affine, i.e. some element of $\bar F$ with $q$-expansion `jqModC` over $\kappa$ has a value in $\kappa$ at that place, and that $\mathrm{ord}(\bar x - s) \le 0$ there for every $s \in S$. Then there is $a \in A$ with $\mathrm{ord}_V(x_j - a) > 0$ and residue $\bar a \notin S$.
--
--   This is the value-lifting half of the dictionary relating $j$ upstairs on $X_H(M)$ to $\tilde\jmath$ on the fibre at $p$: an affine first reading whose reduced $j$-value avoids a finite set $S$ forces an $A$-integral $j$-value upstairs with residue off $S$. It is used in the steps that remove one bad point, in the branches for the $\infty$- and $0$-sides and for the strict first and second readings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_ord_sub_algebraMap_pos_residue_notMem_of_isAffinePlace_reduceFst.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_ord_sub_algebraMap_pos_residue_notMem_of_isAffinePlace_reduceFst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (xj : ↥(xHFunctionFieldBar M H)) (hxj : ((xj : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (S : Finset (ResidueField ↥A)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V))
    (hS : ∀ s ∈ S, ¬ 0 < (Psp.reduceFst α hα V).ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) s)) :
    ∃ a : ↥A, 0 < V.ord (xj - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ∧ IsLocalRing.residue ↥A a ∉ S := by sorry
