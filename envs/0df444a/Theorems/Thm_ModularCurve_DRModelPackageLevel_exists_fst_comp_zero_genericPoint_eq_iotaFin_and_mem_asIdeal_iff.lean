-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
-- name    : ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/7b0767e6-aa34-53ea-bc49-4ee39ac2371d
-- title:
--   The zeroth fibre component meets the finite chart in the Gauss prime
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a term of the structure `DRModelPackageLevel N₀ q hqN` (a Deligne–Rapoport package for the Igusa scheme of level $N_0q$ over `DRLevel.R q`, bundling properness, flatness and integrality of `DRLevel.toBase N₀ q`, local finite presentation, integral closedness of the sections over affine opens, a curve model of the full modular function field over $\overline{\mathbf Q}$ compatible with the Galois action and with $\mathfrak q$-expansions, smoothness and geometric integrality of the generic fibre, cusp sections, and the further data of the structure). Let $W_0$ be a valuation subring of `modularFunctionFieldFull (N₀ * q)`, the subfield of $\mathbf Q((\mathfrak q))$ generated over $\mathbf Q$ by the divisor expansions of level $N_0q$, and assume $W_0$ is the $q$-adic Gauss ring: $f \in W_0$ if and only if there are Laurent series $x, y$ over $\mathbf Z$ with the coefficientwise reduction of $y$ modulo $q$ nonzero and $f \cdot y = x$ in $\mathbf Q((\mathfrak q))$. Let $\kappa$ be an algebraically closed field of characteristic $q$, let $\mathrm{to}\kappa :$ `DRLevel.R q` $\to \kappa$ be a ring homomorphism, and assume the fibre `DRLevel.fibre0 toκ` (the pullback of `DRLevel.toBase0 N₀ q` along $\operatorname{Spec}$ of $\mathrm{to}\kappa$) is an integral scheme. Then there is a prime $\mathfrak q_0$ of the $j$-finite chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q` such that the image in the Igusa scheme, under `pullback.fst`, of the image of the generic point of `DRLevel.fibre0 toκ` under the zeroth labelled component map $\mathfrak P.\mathrm{comp}\,\kappa\,\mathrm{to}\kappa\,0$ equals the image of $\mathfrak q_0$ under `IgusaScheme.ιFin (N₀ * q) q`, and, for every element $b$ of the chart algebra, $b \in \mathfrak q_0$ if and only if $b$ is a non-unit of $W_0$.
--
--   This orients the two labelled copies of the characteristic-$q$ Deligne–Rapoport fibre against the two minimal primes of $(q)$ in the $j$-finite chart: the component indexed by $0$ has generic point the centre in the chart algebra of the $\infty$-Gauss valuation ring $W_0$. It is used in the analysis of stalks and germs along the zeroth component, in particular for the statements on germs of $j_{\mathfrak q}$ and on integrality of $\varphi$ at the generic point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.exists_fst_comp_zero_genericPoint_eq_iotaFin_and_mem_asIdeal_iff
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)

    (W₀ : ValuationSubring ↥(modularFunctionFieldFull (N₀ * q)))
    (hW₀ : ∀ f : ↥(modularFunctionFieldFull (N₀ * q)), f ∈ W₀ ↔
      ∃ x y : LaurentSeries ℤ, coeffMap (Int.castRingHom (ZMod q)) y ≠ 0 ∧
        (f : LaurentSeries ℚ) * coeffMap (Int.castRingHom ℚ) y = coeffMap (Int.castRingHom ℚ) x)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) toκ)] :
    ∃ 𝔮₀ : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
      (pullback.fst (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom toκ))).base
          ((𝔓.comp κ toκ 0).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) toκ))) =
        (IgusaScheme.ιFin (N₀ * q) q).base 𝔮₀ ∧
      ∀ b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q),
        b ∈ 𝔮₀.asIdeal ↔ ((b : ↥(modularFunctionFieldFull (N₀ * q))) ∈ W₀.nonunits) := by sorry
