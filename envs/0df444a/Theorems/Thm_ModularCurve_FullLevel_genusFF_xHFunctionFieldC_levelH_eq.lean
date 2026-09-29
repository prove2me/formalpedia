-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq
-- name    : ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/36f3503e-3e56-5730-ace1-a0e5c310f2ac
-- title:
--   Genus of the level Γ_H(q²M') function field in characteristic q
-- statement:
--   Let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\kappa$ be an algebraically closed field of characteristic $q$. Let $W$ be a finite set of places of the modular function field $\mathrm{modularFunctionFieldC}\ \kappa\ M'$ — the subfield of the Laurent series field $\kappa((X))$ generated over $\kappa$ by the $q$-expansions `jqModC` and `jqNModC` of level $M'$ — and assume that a place lies in $W$ exactly when it lies in $\mathrm{ssPlaces}\ q\ M'\ \kappa$, i.e. satisfies the predicate `IsSupersingularPlace q M' κ`. Then the genus over $\kappa$ of the field $\mathrm{xHFunctionFieldC}\ \kappa\ (q^2M')\ (\mathrm{levelH}\ q\ M')$, namely the $q$-expansion function field of level $\Gamma_H(q^2M')$ for $H$ the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, defined as the $\kappa$-dimension of $H^1$ of the zero divisor, satisfies, as an identity in $\mathbb{Q}$,
--   $$g = 1 + \frac{(q^2-1)\,\psi(M')}{48} - \frac{(q-1)\,\nu_\infty(M')}{4} - \frac{|W|}{2},$$
--   where $\psi(M') = \sum_{d \mid M',\ d \text{ squarefree}} M'/d$ and $\nu_\infty(M') = \sum_{d \mid M'} \varphi(\gcd(d, M'/d))$.
--
--   Classically this computes the genus of the Igusa curve of level $q$ modulo $\pm 1$ over $X_0(M')_\kappa$, the supersingular points contributing the term $|W|/2$; the result is stated here for an arbitrary algebraically closed field of characteristic $q$ rather than for the residue field of a fixed place of $\overline{\mathbb{Q}}$ above $q$. It feeds the genus bookkeeping for the semistable reduction of the full-level modular curve at $q$, being used by [`ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_add_eq_of_igusa_supersingular_charts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_genusFF_xHFunctionFieldC_levelH_eq.lean

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

open ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open AlgebraicCurve
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.genusFF_xHFunctionFieldC_levelH_eq
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ]
    (W : Finset (Place κ (modularFunctionFieldC κ M'))) (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' κ) :
    (AlgebraicCurve.genusFF κ ↥(xHFunctionFieldC κ (q ^ 2 * M') (levelH q M')) : ℚ) =
      1 + ((q : ℚ) ^ 2 - 1) * dedekindPsi M' / 48
        - ((q : ℚ) - 1) * cuspCount M' / 4
        - (W.card : ℚ) / 2 := by sorry
