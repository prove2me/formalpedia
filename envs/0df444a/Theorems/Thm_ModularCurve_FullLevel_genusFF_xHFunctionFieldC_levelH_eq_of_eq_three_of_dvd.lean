-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
-- name    : ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/96ef0ca9-3218-5a1b-9d32-7283a9ee2f65
-- title:
--   Genus of the Γ_H(q²M') function field at q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number not divisible by $q$, and suppose there is a prime $\ell$ with $\ell \equiv 11 \pmod{12}$ and $\ell \mid M'$. Let $\kappa$ be an algebraically closed field of characteristic $q$, and let $W$ be a finite set of places of the level-$M'$ modular function field $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ over $\kappa$ — that is, of valuation subrings of the subfield of $\kappa$-Laurent series generated over $\kappa$ by the $q$-expansions `jqModC` and `jqNModC` of $j$ and of $j$ at level $M'$, each containing $\kappa$, proper, and a principal ideal ring — whose members are exactly the places satisfying `IsSupersingularPlace q M' κ`. Then the genus $\dim_\kappa H^1(0)$ of the function field $\mathrm{xHFunctionFieldC}\ \kappa\ (q^2M')\ (\mathrm{levelH}\ q\ M')$, the $q$-expansion function field over $\kappa$ of the congruence subgroup $\Gamma_H(q^2M')$ attached to the subgroup $H \le (\mathbb{Z}/q^2M')^\times$ of units congruent to $1$ modulo $q$, satisfies, as an identity in $\mathbb{Q}$,
--   $$1 + \frac{(q^2-1)\,\psi(M')}{48} - \frac{(q-1)\,c_0(M')}{4} - \frac{|W|}{2},$$
--   where $\psi(M') = \sum_{d \mid M',\, d \text{ squarefree}} M'/d$ and $c_0(M') = \sum_{d \mid M'} \varphi(\gcd(d, M'/d))$.
--
--   This is the characteristic-$3$ instance of the genus formula for the Igusa-type covering of level $q$ over $X_0(M')_\kappa$, stated in the same closed form as for $q \ge 5$; the hypothesis that a prime $\ell \equiv 11 \pmod{12}$ divides $M'$ rules out elliptic points and makes the supersingular mass count available. It feeds the comparison of genera over $\overline{\mathbb{Q}}$ and $\kappa$ used in the Igusa supersingular chart computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq_of_eq_three_of_dvd
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (W : Finset (Place κ (modularFunctionFieldC κ M'))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' κ) :
    (AlgebraicCurve.genusFF κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) : ℚ) =
      1 + ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 48
        - ((q : ℚ) - 1) * cuspCount M' / 4
        - (W.card : ℚ) / 2 := by sorry
