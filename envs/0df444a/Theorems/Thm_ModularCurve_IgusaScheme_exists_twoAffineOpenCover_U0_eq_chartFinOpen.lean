-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- name    : ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/79a5a757-c842-5bc5-9b94-ffc3f29bce9f
-- title:
--   The Igusa scheme has a two-affine open cover by its charts
-- statement:
--   Let $N$ be a nonzero natural number and $\ell$ a prime. Write $\mathfrak{X} =$ `IgusaScheme N ℓ` for the scheme obtained as the pushout, in the category of schemes, of the two morphisms `fFin N ℓ` and `fInf N ℓ` out of `XMid N ℓ`, these being the morphisms of affine schemes $\mathrm{Spec}$-dual to the ring maps `inclFin N ℓ` and `inclInf N ℓ` into the middle chart. Let `chartFinOpen N ℓ` and `chartInfOpen N ℓ` be the open subsets of $\mathfrak{X}$ given by the ranges of the two structural morphisms `ιFin N ℓ` and `ιInf N ℓ` into the pushout. The assertion is that there exists a term $\mathcal{V}$ of the structure `Scheme.TwoAffineOpenCover` for $\mathfrak{X}$ — that is, a pair of open subsets $U_0, U_1 \subseteq \mathfrak{X}$ together with proofs that $U_0$ is affine, that $U_1$ is affine, that $U_0 \sqcup U_1 = \top$, and that $U_0 \sqcap U_1$ is affine — whose two members are exactly the two charts: $\mathcal{V}.U_0 =$ `chartFinOpen N ℓ` and $\mathcal{V}.U_1 =$ `chartInfOpen N ℓ`.
--
--   This packages the two Igusa charts of the integral model of the modular curve into the interface used by the representability results for relative Picard functors: the model is covered by two affine opens whose intersection is again affine. It is cited in the development of the Deligne–Rapoport model package, in particular by [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic), [`ModularCurve.DRModelPackageLevel.bijective_algebraMap_sections_baseChange`](thm.html#ModularCurve.DRModelPackageLevel.bijective_algebraMap_sections_baseChange) and [`ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero`](thm.html#ModularCurve.DRModelPackageLevel.nonempty_iso_unit_fibre_of_isAlgEquivZero_of_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_twoAffineOpenCover_U0_eq_chartFinOpen.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.exists_twoAffineOpenCover_U0_eq_chartFinOpen (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ 𝒱 : (IgusaScheme N ℓ).TwoAffineOpenCover, 𝒱.U0 = chartFinOpen N ℓ ∧ 𝒱.U1 = chartInfOpen N ℓ := by sorry
