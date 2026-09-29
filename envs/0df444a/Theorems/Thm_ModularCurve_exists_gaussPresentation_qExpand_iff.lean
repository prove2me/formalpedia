-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussPresentation_qExpand_iff
-- name    : ModularCurve.exists_gaussPresentation_qExpand_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/a43c4a37-92a9-5431-9960-16b20e157263
-- title:
--   Gauss presentations are invariant under q ↦ q^N
-- statement:
--   Let $A$ be a commutative local ring, let $L$ be a field equipped with an $A$-algebra structure, and let $N$ be a nonzero natural number. For a Laurent series $g \in L((q))$, i.e. an element of `LaurentSeries L` (Hahn series over $L$ with value group $\mathbb{Z}$), write $g(q^N)$ for [`ModularCurve.qExpand L N g`](def/ModularCurve_X0.html#L25), the image of $g$ under the ring homomorphism obtained by transporting the support along multiplication by $N$ on $\mathbb{Z}$, so that the coefficient of $q^{Nn}$ in $g(q^N)$ is the coefficient of $q^n$ in $g$ and all other coefficients vanish. Say that $h \in L((q))$ admits a *Gauss presentation* if there are power series $x, y \in A[[q]]$ such that the reduction of $y$ under the residue map of $A$ to its residue field is nonzero and $h \cdot \hat y = \hat x$, where $\hat{\;\cdot\;}$ denotes the image in $L((q))$ of the power series obtained by applying $A \to L$ coefficientwise, via `HahnSeries.ofPowerSeries`. The theorem asserts that $g(q^N)$ admits a Gauss presentation if and only if $g$ does.
--
--   For $A$ a discrete valuation ring with fraction field $L$, the Laurent series admitting a Gauss presentation form the valuation ring of $A$-integral $q$-expansions attached to the $\infty$-component of the special fibre of a modular curve in the $q$-expansion model; the statement says that this set of series is its own preimage under the degeneracy substitution $q \mapsto q^N$. It is used in [`ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH`](thm.html#ModularCurve.FullLevel.map_jChartFin_mem_ssJSet_of_comap_gauss_ne_gauss_of_forall_mem_nonunits_xH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussPresentation_qExpand_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_gaussPresentation_qExpand_iff
    (A : Type) [CommRing A] [IsLocalRing A] (L : Type) [Field L] [Algebra A L]
    (N : ℕ) [NeZero N] (g : LaurentSeries L) :
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      ModularCurve.qExpand L N g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) ↔
    (∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      g * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) := by sorry
