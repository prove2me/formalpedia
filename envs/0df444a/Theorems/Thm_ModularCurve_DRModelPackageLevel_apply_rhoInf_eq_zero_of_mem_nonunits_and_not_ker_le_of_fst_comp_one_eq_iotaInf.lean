-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
-- name    : ModularCurve.DRModelPackageLevel.apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/2243bee8-72c6-5636-bad1-d40f2bc3a172
-- title:
--   Retraction ρ_∞ kills W₀-nonunits, misses the second component
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, and assume $q \nmid N_0$; let $\mathfrak P$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for level $N_0 q$. Let $W_0$ be a valuation subring of the modular function field `modularFunctionFieldFull (N₀ * q)` (the subfield of $\mathrm{LaurentSeries}\ \mathbb Q$ generated over $\mathbb Q$ by the divisor expansions of level $N_0q$), subject to the hypothesis that $f \in W_0$ holds exactly when there are Laurent series $x,y$ with integer coefficients such that the coefficientwise reduction of $y$ modulo $q$ is nonzero and $f \cdot y = x$ after coefficientwise inclusion of $\mathbb Z$ into $\mathbb Q$. Let $\kappa$ be an algebraically closed field of characteristic $q$ and $\mathrm{to}\kappa : \mathrm{R}\,q \to \kappa$ a ring homomorphism such that the scheme `DRLevel.fibre0 toκ`, the pullback of `DRLevel.toBase0 N₀ q` along $\mathrm{Spec}\,\mathrm{to}\kappa$, is integral. Two conclusions are asserted. First, for every element $b$ of the chart algebra `IgusaScheme.chartAlgInf (N₀ * q) q` (the subalgebra of the modular function field attached to $j^{-1}$) whose image in the modular function field is a non-unit of $W_0$, one has $\mathrm{to}\kappa(\mathfrak P.\mathrm{rhoInf}\, b) = 0$. Second, for every prime $\mathfrak r$ of that chart algebra, if the component morphism $\mathfrak P.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,1$ followed by the first pullback projection of `DRLevel.toBase N₀ q` along $\mathrm{Spec}\,\mathrm{to}\kappa$ carries the generic point of `DRLevel.fibre0 toκ` to the image of $\mathfrak r$ under the chart immersion `IgusaScheme.ιInf (N₀ * q) q`, then the ideal of $\mathfrak r$ is not contained in the kernel of $\mathrm{to}\kappa \circ \mathfrak P.\mathrm{rhoInf}$.
--
--   This is the orientation statement for the two components of the characteristic-$q$ fibre of the Igusa model of $X_0(N_0q)$: it records that the package's retraction at the cusp $\infty$ annihilates the non-units of the $q$-adic Gauss ring $W_0$ of the expansion at $\infty$, while the prime lying under the generic point of the component labelled $1$ escapes that kernel. It is used, together with the dictionary between points of the pole chart and the minimal primes over $q$, to identify the component labelled $0$ as the one carrying the $\infty$-Gauss centre, in [`ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff`](thm.html#ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.apply_rhoInf_eq_zero_of_mem_nonunits_and_not_ker_le_of_fst_comp_one_eq_iotaInf
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (W₀ : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    (∀ b : ↥(IgusaScheme.chartAlgInf (N₀ * q) q), ((b : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W₀.nonunits) → toκ (𝔓.rhoInf b) = 0) ∧
    (∀ 𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf (N₀ * q) q),
      (𝔓.comp κ toκ 1 ≫ pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ)) =
        (IgusaScheme.ιInf (N₀ * q) q).base 𝔯 →
      ¬ (𝔯.asIdeal ≤ RingHom.ker (toκ.comp 𝔓.rhoInf.toRingHom))) := by sorry
