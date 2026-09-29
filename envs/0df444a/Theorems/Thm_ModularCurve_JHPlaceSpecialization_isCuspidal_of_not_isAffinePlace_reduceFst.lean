-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst
-- name    : ModularCurve.JHPlaceSpecialization.isCuspidal_of_not_isAffinePlace_reduceFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/65171477-3641-527c-beb3-9f78ce16835e
-- title:
--   Places with non-affine first reduction are cuspidal
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$ (so that $M/p$ is again nonzero), and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense of `LiesOverPrime`, that is, $p$ is a nonunit of $A$, and assume its residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $FM =$ `xHFunctionFieldBar M H` and $FMp =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` for the $\overline{\mathbb{Q}}$-base changes, inside $\overline{\mathbb{Q}}$-Laurent series, of the $q$-expansion function fields of level $\Gamma_H(M)$ and of level $\Gamma_{H'}(M/p)$, where $H'$ is the image of $H$ under `ZMod.unitsMap`. Let $\alpha : FMp \to FM$ be an integral $\overline{\mathbb{Q}}$-algebra map which preserves $q$-expansions, i.e. $\alpha u$ and $u$ have the same underlying Laurent series for all $u$. Let $Psp$ be a `JHPlaceSpecialization` for these data: a map $\mathrm{sp}$ from places of $FMp$ over $\overline{\mathbb{Q}}$ to places of the fibre field $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$ (a place being a proper valuation subring containing the base field and a principal ideal ring), together with a map on degree-zero divisor classes, the divisor-level $q$-expansion dictionary sending $\mathrm{sp}_*\operatorname{div} f$ to $\operatorname{div} g$ whenever $f$ has an $A$-integral $q$-expansion with nonzero coefficientwise reduction $g$, surjectivity of $\mathrm{sp}$, the divisor-lifting property, invariance under the inertia subgroup at $A$, compatibility with Frobenius via `qExpFrobeniusPlaceModL`, and compatibility of the two maps on $\mathrm{Pic}^0$. Let $V$ be a place of $FM$ over $\overline{\mathbb{Q}}$ and suppose that $Psp.\mathrm{reduceFst}\,\alpha\,h\alpha\,V = \mathrm{sp}(V|_\alpha)$, the restriction of $V$ along $\alpha$ pushed through $\mathrm{sp}$, is not an affine place, i.e. there are no $x \in \bar F$ with Laurent series `jqModC κ` and $a \in \kappa$ such that $x$ lies in that place's valuation ring with residue the image of $a$. Then $V$ is cuspidal: for every $x \in FM$ whose Laurent series is `jqModC (AlgebraicClosure ℚ)` and every $a \in A$, one has $\operatorname{ord}_V\bigl(x - \alpha_{FM}(a)\bigr) \le 0$, where $\alpha_{FM}$ is the structure map $\overline{\mathbb{Q}} \to FM$.
--
--   This is the pointwise half of the cusp dictionary for the specialization of places of $X_H(M)$ at a place above $p$ with $p \parallel M$: a place of the characteristic-zero function field at which some value of $j$ would be attained must reduce to an affine place of the fibre field, so a place with non-affine first reduction is a pole of $j$, i.e. a cusp. It is used in the construction of prolongation data, where places with prescribed order one and with non-cuspidal, strict reductions on both sides are produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_not_isAffinePlace_reduceFst.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

open Classical in

theorem ModularCurve.JHPlaceSpecialization.isCuspidal_of_not_isAffinePlace_reduceFst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hV : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V)) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by sorry
