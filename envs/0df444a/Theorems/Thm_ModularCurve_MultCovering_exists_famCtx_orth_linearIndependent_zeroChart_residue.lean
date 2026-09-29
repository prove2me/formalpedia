-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_famCtx_orth_linearIndependent_zeroChart_residue
-- name    : ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/5345020b-9cb9-55bb-81c5-c975c01e32e6
-- title:
--   A good-family context orthogonal at both cusps exists
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $r \in \mathbb{N}$, and let $s : \mathrm{Fin}\,r \to \overline{\mathbb{Q}}$-modular function field $\mathrm{modularFunctionFieldBar}(1\cdot p)$ be an embedding basis, i.e. $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v))\ \text{for all places } v\}$ of the divisor $\mathrm{embDivisor}(1\cdot p)$. Then there is a family context $\Phi : \mathrm{FamCtx}\ p\ r$ — a $\mathrm{FamData}$ whose members $t$ again form such an embedding basis, with $t_l = 1$ for $l = 0$, and with the prescribed integrality and residue descriptions at the chart at infinity and at the zero chart — satisfying three further properties. First, for every $c : \mathrm{Fin}\,r \to \mathbb{Q}$, all Laurent coefficients of $\sum_i c_i \cdot \Phi.\mathrm{tRat}_i \in \mathrm{modularFunctionFieldFull}(1\cdot p) \subseteq \mathbb{Q}((q))$ have non-negative $p$-adic valuation if and only if every $c_i$ does. Second, for every such $c$, all Laurent coefficients of $\sum_i c_i \cdot w_p(\Phi.\mathrm{tRat}_i)$, with $w_p = \mathrm{frickeInvolutionFull}(1\cdot p)$, have non-negative $p$-adic valuation if and only if $v_p(c_i) \ge -n_i$ for all $i$, where $n_i = \mathrm{hasseExp}\ \Phi.\mathrm{toFamData}\ i$. Third, for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and residue field of characteristic $p$, and every chart context $\Gamma : \mathrm{ChartCtx}\ p\ A$, the rescaled members $\mathrm{goodFamilyZero}\ \Phi.\mathrm{toFamData}\ l = p^{-n_l} t_l$ all lie in the valuation subring of integers of the zero chart $(\mathrm{infChart}\ \Gamma)$ pulled back along the Fricke involution, and their residues are linearly independent over the residue field of $A$.
--
--   This is the existence statement for a good family of functions on $X_0(p)$ adapted simultaneously to the two Gauss valuations attached to the cusps, together with the consequence, at every prime of $\overline{\mathbb{Q}}$ above $p$, that the $p$-power rescalings of the family reduce to a linearly independent system on the component of the chart at $\bar 0$. It is used by the cross-comparison lemmas that match annulus data with annulus and with zero-chart data in the analysis of the reduction of $X_0(p)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_famCtx_orth_linearIndependent_zeroChart_residue.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_famCtx_orth_linearIndependent_zeroChart_residue
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    ∃ Φ : ModularCurve.MultCovering.FamCtx p r,
      (∀ c : Fin r → ℚ,
        (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • Φ.toFamData.tRat i : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
          ↔ ∀ i, 0 ≤ padicValRat p (c i)) ∧
      (∀ c : Fin r → ℚ,
        (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (Φ.toFamData.tRat i) :
            ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
          ↔ ∀ i, -((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p (c i)) ∧
      ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
        [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
        ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
          LinearIndependent (IsLocalRing.ResidueField ↥A)
            (fun l => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
