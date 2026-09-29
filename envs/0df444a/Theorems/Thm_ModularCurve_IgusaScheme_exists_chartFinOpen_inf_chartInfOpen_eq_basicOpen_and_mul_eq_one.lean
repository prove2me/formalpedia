-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one
-- name    : ModularCurve.IgusaScheme.exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/32e790ec-15f0-5716-bebf-2f35a97abf23
-- title:
--   Two-chart datum for the Igusa scheme: overlap is a basic open
-- statement:
--   Fix a natural number $N$ with $N \neq 0$ and a prime $\ell$. Write $\mathfrak{X} =$ `IgusaScheme N ℓ` for the scheme obtained as the pushout of the two morphisms $\mathrm{fFin} \colon \mathrm{XMid}(N,\ell) \to \mathrm{XFin}(N,\ell)$ and $\mathrm{fInf} \colon \mathrm{XMid}(N,\ell) \to \mathrm{XInf}(N,\ell)$, each of these being the morphism of affine spectra induced by the ring inclusion `inclFin N ℓ`, respectively `inclInf N ℓ`. Let $U_0 =$ `chartFinOpen N ℓ` and $U_1 =$ `chartInfOpen N ℓ` be the open subsets of $\mathfrak{X}$ given by the ranges of the chart morphisms `ιFin N ℓ` and `ιInf N ℓ`. The assertion is that there exist a section $f \in \Gamma(\mathfrak{X}, U_0)$ and a section $g \in \Gamma(\mathfrak{X}, U_1)$ such that the intersection $U_0 \cap U_1$ (the meet in the lattice of opens of $\mathfrak{X}$) coincides both with the basic open subset $D(f)$ determined by $f$ and with the basic open subset $D(g)$ determined by $g$, and such that the restriction of $f$ along the inclusion $U_0 \cap U_1 \le U_0$ times the restriction of $g$ along the inclusion $U_0 \cap U_1 \le U_1$ equals $1$ in $\Gamma(\mathfrak{X}, U_0 \cap U_1)$. No further hypotheses are imposed.
--
--   This records the standard datum of a scheme glued from two affine charts along a principal open: on the Igusa model the two charts meet in the locus where the $j$-invariant (respectively its inverse) is invertible, and the two sections are mutually inverse there. It is the hypothesis package used by [`ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen`](thm.html#ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen) and, through it, by [`ModularCurve.DRModelPackageLevel.exists_isAffineOpen_of_finset_smoothLocus`](thm.html#ModularCurve.DRModelPackageLevel.exists_isAffineOpen_of_finset_smoothLocus), which produces a single affine open containing a prescribed finite set of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_chartFinOpen_inf_chartInfOpen_eq_basicOpen_and_mul_eq_one (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (f : Γ(IgusaScheme N ℓ, chartFinOpen N ℓ)) (g : Γ(IgusaScheme N ℓ, chartInfOpen N ℓ)),
      chartFinOpen N ℓ ⊓ chartInfOpen N ℓ = (IgusaScheme N ℓ).basicOpen f ∧
      chartFinOpen N ℓ ⊓ chartInfOpen N ℓ = (IgusaScheme N ℓ).basicOpen g ∧
      ((IgusaScheme N ℓ).presheaf.map (homOfLE (inf_le_left : chartFinOpen N ℓ ⊓ chartInfOpen N ℓ ≤ chartFinOpen N ℓ)).op).hom f *
        ((IgusaScheme N ℓ).presheaf.map (homOfLE (inf_le_right : chartFinOpen N ℓ ⊓ chartInfOpen N ℓ ≤ chartInfOpen N ℓ)).op).hom g
          = 1 := by sorry
