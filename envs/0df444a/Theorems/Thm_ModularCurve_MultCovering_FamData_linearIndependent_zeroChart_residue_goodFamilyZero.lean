-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero
-- name    : ModularCurve.MultCovering.FamData.linearIndependent_zeroChart_residue_goodFamilyZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/cded60bb-f523-50e2-841a-5a56feede4f9
-- title:
--   Linear independence of the zero-chart residues of a Gauss-orthogonal family
-- statement:
--   Let $p$ be a prime, $r$ a natural number, and $D$ a datum of type `FamData p r`: a family $t_l$ ($l \in \mathrm{Fin}\,r$) of elements of the base-changed modular function field $\overline{F}(1\cdot p)$ inside $\overline{\mathbb Q}((q))$, together with rational representatives $t_l^{\mathbb Q}$ in $F_{\mathrm{full}}(1\cdot p) \subseteq \mathbb Q((q))$ such that each $t_l$ is the coefficientwise image of $t_l^{\mathbb Q}$. Assume the orthogonality hypothesis: for every $c : \mathrm{Fin}\,r \to \mathbb Q$, all coefficients of the Laurent series $\sum_i c_i\,w_p(t_i^{\mathbb Q})$ have non-negative $p$-adic valuation, where $w_p$ is `frickeInvolutionFull (1 * p)`, if and only if $v_p(c_i) \ge -n_i$ for all $i$, with $n_i =$ `hasseExp D i`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ (the predicate `LiesOverPrime`), with residue field of characteristic $p$, and let $\Gamma$ be a chart context `ChartCtx p A` (modular polynomial data with Kronecker congruence, integrality of the Hecke operators $\bar\alpha,\bar\beta$, a place specialisation and a level-one prolongation pair, a set $S_1$ of places, the finset of supersingular places, the finiteness and cardinality data for the supersingular $j$-set, and a chart-first supply). Write `zeroChart` $\Gamma$ for the transport along `frickeInvolutionBar (1 * p)` of the infinity chart of $\Gamma$, and assume each $p^{-n_l} t_l$, namely `goodFamilyZero D l`, lies in the valuation subring of integers of that chart. Then the family of residues of these elements under the chart's residue map is linearly independent over the residue field of $A$.
--
--   This is the zero-component counterpart of the statement that a $p$-saturated, $p$-integrally normalised family of modular functions of level $p$ reduces to a linearly independent family on a component of the fibre at $p$. It is used by [`ModularCurve.MultCovering.FamData.t_zeroChart_of_orth`](thm.html#ModularCurve.MultCovering.FamData.t_zeroChart_of_orth) and by [`ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue`](thm.html#ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue) in assembling the family data attached to the two components of $X_0(p)$ over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_linearIndependent_zeroChart_residue_goodFamilyZero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.linearIndependent_zeroChart_residue_goodFamilyZero
    (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
          ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l => (zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by sorry
