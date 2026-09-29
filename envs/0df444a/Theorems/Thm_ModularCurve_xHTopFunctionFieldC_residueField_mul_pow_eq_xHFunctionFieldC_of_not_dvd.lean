-- Prove2me | Theorems.Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
-- name    : ModularCurve.xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/d94f249a-035c-58e4-a8c9-c7737a0c531a
-- title:
--   Mod ℓ collapse of Γ₀(ℓ^r)-level q-expansion function fields
-- statement:
--   Fix an integer $N$ with $N \neq 0$ and a subgroup $H \le (\mathbb{Z}/N\mathbb{Z})^{\times}$, a prime $\ell$ with $\ell \nmid N$, and an arbitrary natural number $r$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which `LiesOverPrime ℓ`, meaning that the image of $\ell$ in $\overline{\mathbb{Q}}$ lies in the non-units of $A$, and write $k =$ `IsLocalRing.ResidueField A` for its residue field. For a subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$, [`ModularCurve.qExpFunctionFieldC k Γ`](def/ModularCurve_X1.html#L101) denotes the intermediate field of the Laurent series field $k((q))$ obtained by adjoining to $k$ the set [`ModularCurve.intFormRatiosC k Γ`](def/ModularCurve_X1.html#L83) of $q$-expansions attached to $\Gamma$ over $k$; here $\Gamma$ is taken to be [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133), the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those elements of $\Gamma_0(N)$ whose associated unit `gamma0Units N` lies in $H$, respectively its intersection with $\Gamma_0(N\ell^r)$. The assertion is the equality of intermediate fields of $k((q))$ $$\mathrm{qExpFunctionFieldC}\,k\,\bigl(\Gamma_H(N) \cap \Gamma_0(N\ell^r)\bigr) = \mathrm{qExpFunctionFieldC}\,k\,\bigl(\Gamma_H(N)\bigr),$$ i.e. `xHTopFunctionFieldC k N H (N * ℓ ^ r) = xHFunctionFieldC k N H`.
--
--   In characteristic zero the left-hand field is a proper extension of the right-hand one of degree $\ell^{r-1}(\ell+1)$ for $r \ge 1$; the statement records that after reduction at a place of $\overline{\mathbb{Q}}$ above $\ell$, with $\ell$ prime to $N$, the $\Gamma_0(\ell^r)$-part of the level contributes nothing to the $q$-expansion function field at the cusp $\infty$. It is used in the identification of the level-$H$ $q$-expansion function field at full level with the modular function field over a residue field at a place above $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.xHTopFunctionFieldC_residueField_mul_pow_eq_xHFunctionFieldC_of_not_dvd
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) (r : ℕ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ModularCurve.xHTopFunctionFieldC (IsLocalRing.ResidueField A) N H (N * ℓ ^ r) =
      ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) N H := by sorry
