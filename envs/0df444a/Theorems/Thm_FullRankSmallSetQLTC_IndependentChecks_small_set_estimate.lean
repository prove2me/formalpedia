-- Prove2me | Theorems.Thm_FullRankSmallSetQLTC_IndependentChecks_small_set_estimate
-- name    : FullRankSmallSetQLTC.IndependentChecks.small_set_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:50.433005+00:00
-- url     : https://prove2.me/theorems/e5becb26-d8ad-4a25-98b9-ed40056240a2
-- title:
--   Section 5.3, equation (5.1) — weighted small-set estimate, both orientations
-- statement:
--   Fix degrees $D_1,D_1',D_2,D_2'$, densities $c_1,c_2>0$ and orbit counts. There is $\kappa>0$, depending only on these, with the following property. Let $\Gamma_A=(A_0,A_1,E_A)$ be two-sided $(c_1,\varepsilon_1)$-lossless with degrees $D_1$ on $A_0$ and $D_1'$ on $A_1$, and $\Gamma_B=(B_0,B_1,E_B)$ two-sided $(c_2,\varepsilon_2)$-lossless with degrees $D_2$ on $B_0$ and $D_2'$ on $B_1$, with a common free action of a finite group $G$ with the given orbit counts. In the balanced-product code (qubits $V_{10}\sqcup V_{01}$) put, for $y=(y_{10},y_{01})$,
--   $$|y|_w=\frac{|y_{10}|}{D_1}+\frac{|y_{01}|}{D_2},$$
--   and call $y$ locally minimal if adding a row of $H_X$ to $y$ does not decrease $|y|_w$.
--
--   1. If $\varepsilon_1\le\varepsilon$, $\varepsilon_1D_1\le D_1'$ and $\varepsilon_2D_1\le\varepsilon$, then every locally minimal $y$ with $|y_{10}|,|y_{01}|<\kappa|G|$ satisfies
--   $$|H_Zy|\ge\Big(\frac12-6\varepsilon\Big)D_1D_2|y|_w .\tag{5.1}$$
--   2. (Reversing both bipartitions exchanges $H_X$ with $H_Z$ and $D_i$ with $D_i'$.) If $\varepsilon_1\le\varepsilon$, $\varepsilon_1D_1'\le D_1$ and $\varepsilon_2D_1'\le\varepsilon$, then every $z=(z_{10},z_{01})$ that is locally minimal for $|z|'_w=|z_{10}|/D_2'+|z_{01}|/D_1'$ under adding rows of $H_Z$, with $|z_{10}|,|z_{01}|<\kappa|G|$, satisfies $|H_Xz|\ge(\frac12-6\varepsilon)D_1'D_2'|z|'_w$.
--
--   This is the Lin–Hsieh estimate ([LH22, Lemma 12]) that yields small-set soundness in Theorem 1.2.
--
--   Differences from the source:
--   - reading: densities c₁, c₂ (sign not stated) → 0 < c₁ and 0 < c₂; reason: the source's lossless densities are always positive constants (Theorems 1.1, 5.1, 5.2); for c ≤ 0 the losslessness predicate is vacuous and the estimate fails (a G-equivariant disjoint union of copies of a fixed graph yields constant-weight logical operators)
--   - encoding: |y|_w = |y₁₀|/D₁ + |y₀₁|/D₂ (and the reversed norm) → the hypotheses 0 < D₁, 0 < D₂ for item 1 and 0 < D₁', 0 < D₂' for item 2; reason: these only exclude the undefined divisions by zero
--   - encoding: Reversing both bipartitions exchanges H_X with H_Z and D_i with D_i' → item 2 written for the original code: the reversed graphs (A₁, A₀), (B₁, B₀) have V'₁₀ = V₀₁, V'₀₁ = V₁₀, H'_X = H_Z and H'_Z = H_X up to the order of the two qubit blocks, so the reversed weight is |z₁₀|/D₂' + |z₀₁|/D₁' and the reversed hypotheses are ε₁ ≤ ε, ε₁D₁' ≤ D₁, ε₂D₁' ≤ ε; reason: direct substitution of the reversed graphs into item 1; one κ serves both orientations (take the minimum)
--   - encoding: κ depends only on the degrees, the densities and the orbit counts → ∃ κ > 0 after fixing these, then ∀ finite groups G, graphs and losses ε₁, ε₂, ε; reason: the source's quantifier order
--   - encoding: arbitrary finite groups and vertex sets → groups and vertex types in Lean's `Type` (universe 0); reason: standard universe convention; every finite instance has a copy in Type
-- source:
--   Yali Aharon Holzman, Michael Ilan, Assaf Reiner, Amnon Ta-Shma, Full-Rank Constructions of Explicit Lossless Expanders and Good Small-Set qLTCs, STOC 2027 submission #692 (October 2026), §5.3, eq. (5.1), p. 26 (printed page = PDF page)

import Mathlib
import Definitions.Def_FullRankSmallSetQLTC_IndependentChecks_BalancedProduct

set_option autoImplicit false

namespace FullRankSmallSetQLTC.IndependentChecks

open MulAction Matrix

open Classical in
/-- **Section 5.3, equation (5.1)** ([LH22, Lemma 12], p. 26), in both orientations.
Fix degrees `D₁, D₁', D₂, D₂'`, densities `c₁, c₂ > 0` and orbit counts. There is `κ > 0`
depending only on these such that the following holds for every finite group `G` and every pair
of bipartite graphs `Γ_A` (degrees `D₁` on `A₀`, `D₁'` on `A₁`, two-sided `(c₁, ε₁)`-lossless) and
`Γ_B` (degrees `D₂` on `B₀`, `D₂'` on `B₁`, two-sided `(c₂, ε₂)`-lossless) with a common free
`G`-action having the given orbit counts.

1. If `ε₁ ≤ ε`, `ε₁D₁ ≤ D₁'`, `ε₂D₁ ≤ ε`, then every `y = (y₁₀, y₀₁)` that is locally minimal for
   `|y|_w = |y₁₀|/D₁ + |y₀₁|/D₂` under adding rows of `H_X`, with `|y₁₀|, |y₀₁| < κ|G|`, satisfies
   `|H_Z y| ≥ (1/2 − 6ε) D₁D₂ |y|_w`.
2. (Reversed bipartitions: `H_X ↔ H_Z`, `D_i ↔ D_i'`.) If `ε₁ ≤ ε`, `ε₁D₁' ≤ D₁`, `ε₂D₁' ≤ ε`,
   then every `z = (z₁₀, z₀₁)` locally minimal for `|z|'_w = |z₁₀|/D₂' + |z₀₁|/D₁'` under adding
   rows of `H_Z`, with `|z₁₀|, |z₀₁| < κ|G|`, satisfies `|H_X z| ≥ (1/2 − 6ε) D₁'D₂' |z|'_w`. -/
theorem small_set_estimate (D₁ D₁' D₂ D₂' : ℕ) (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (nA₀ nA₁ nB₀ nB₁ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (G : Type) [Group G] [Fintype G] (A₀ A₁ B₀ B₁ : Type)
        [MulAction G A₀] [MulAction G A₁] [MulAction G B₀] [MulAction G B₁]
        [Fintype A₀] [Fintype A₁] [Fintype B₀] [Fintype B₁]
        [DecidableEq A₀] [DecidableEq A₁] [DecidableEq B₀] [DecidableEq B₁]
        (adjA : A₀ → A₁ → Prop) [DecidableRel adjA] (adjB : B₀ → B₁ → Prop) [DecidableRel adjB]
        (ε₁ ε₂ ε : ℝ),
        IsFreeAction G A₀ → IsFreeAction G A₁ → IsFreeAction G B₀ → IsFreeAction G B₁ →
        IsInvariantRel G adjA → IsInvariantRel G adjB →
        Fintype.card (orbitRel.Quotient G A₀) = nA₀ →
        Fintype.card (orbitRel.Quotient G A₁) = nA₁ →
        Fintype.card (orbitRel.Quotient G B₀) = nB₀ →
        Fintype.card (orbitRel.Quotient G B₁) = nB₁ →
        IsTwoSidedLossless adjA D₁ D₁' c₁ ε₁ →
        IsTwoSidedLossless adjB D₂ D₂' c₂ ε₂ →
        ((0 < D₁ → 0 < D₂ → ε₁ ≤ ε → ε₁ * D₁ ≤ D₁' → ε₂ * D₁ ≤ ε →
          ∀ y : BPQubit G (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁) → ZMod 2,
            IsLocallyMinimal (bpHX G adjA adjB) (blockWeight D₁ D₂) y →
            (hammingNorm (fun v => y (Sum.inl v)) : ℝ) < κ * Fintype.card G →
            (hammingNorm (fun v => y (Sum.inr v)) : ℝ) < κ * Fintype.card G →
            (1 / 2 - 6 * ε) * D₁ * D₂ * blockWeight D₁ D₂ y ≤
              (hammingNorm (bpHZ G adjA adjB *ᵥ y) : ℝ)) ∧
         (0 < D₁' → 0 < D₂' → ε₁ ≤ ε → ε₁ * D₁' ≤ D₁ → ε₂ * D₁' ≤ ε →
          ∀ z : BPQubit G (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁) → ZMod 2,
            IsLocallyMinimal (bpHZ G adjA adjB) (blockWeight D₂' D₁') z →
            (hammingNorm (fun v => z (Sum.inl v)) : ℝ) < κ * Fintype.card G →
            (hammingNorm (fun v => z (Sum.inr v)) : ℝ) < κ * Fintype.card G →
            (1 / 2 - 6 * ε) * D₁' * D₂' * blockWeight D₂' D₁' z ≤
              (hammingNorm (bpHX G adjA adjB *ᵥ z) : ℝ))) := by sorry

end FullRankSmallSetQLTC.IndependentChecks
