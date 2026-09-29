-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackage_isInvertible_comap_comp_subschemeIotaV4
-- name    : ModularCurve.DRResolvedModelPackage.isInvertible_comap_comp_subschemeIotaV4
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:14.444979+00:00
-- url     : https://prove2.me/theorems/18d1a6c0-b989-515c-b714-acf1a1a3bf23
-- title:
--   Invertibility of the ideal of Cᵥ restricted to C_w
-- statement:
--   Fix a prime $p$, a package $\mathfrak{X}$ of Deligne–Rapoport model data `DRModelPackage p`, a commutative ring $O$, an algebraically closed field $\kappa$ of characteristic $p$, a ring homomorphism $toκ : O \to \kappa$, and a resolved-model package $R$ of type `DRResolvedModelPackage p 𝔛 O κ toκ`; among the data of $R$ are a scheme $Y$ proper and flat over $\operatorname{Spec} O$ with the regularity and dimension conditions away from the locus where $p$ is invertible, a finite type `node` of nodes with widths `R.width`, and, for each index $v$ in `X0MqComponents R.width` $= \mathrm{Fin}\,2 \sqcup \bigl(\Sigma\,n,\ \mathrm{Fin}(\mathrm{width}\,n - 1)\bigr)$, an ideal sheaf datum `R.comp v` on $Y$ which is invertible and whose associated closed subscheme is integral. Let $v, w$ be two such indices with $v \neq w$. The conclusion is that the ideal sheaf datum obtained by pulling back `R.comp v` along the closed immersion `(R.comp w).subschemeι` of the closed subscheme cut out by `R.comp w` satisfies `IsInvertible`: for every point $x$ of that subscheme there are an affine open $U$ and a section $f \in \Gamma(U)$ with $x$ in the basic open set $D(f)$, together with a non-zero-divisor $g$ of $\Gamma(D(f))$ generating the ideal of the pulled-back datum on the affine open $D(f)$.
--
--   This is the statement that the restriction to one component $C_w$ of the special fibre of the divisor cut out by another component $C_v$ is an effective Cartier divisor on $C_w$, the hypothesis needed to compute intersection numbers $(C_v \cdot C_w)$ on the regular model as degrees of line bundles. It feeds the Euler-characteristic computation [`ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4`](thm.html#ModularCurve.DRResolvedModelPackage.eulerChar_sectionsOf_pullback_invModule_comp_eq_add_x0MqAdjV4).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackage_isInvertible_comap_comp_subschemeIotaV4.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicCurve_RelCartier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.DRResolvedModelPackage.isInvertible_comap_comp_subschemeIotaV4
    (p : ℕ) [Fact p.Prime] {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ} (R : DRResolvedModelPackage p 𝔛 O κ toκ)
    (v w : X0MqComponents R.width) (hvw : v ≠ w) :
    ((R.comp v).comap (R.comp w).subschemeι).IsInvertible := by sorry
