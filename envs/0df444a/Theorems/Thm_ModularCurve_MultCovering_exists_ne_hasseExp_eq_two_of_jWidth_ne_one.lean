-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one
-- name    : ModularCurve.MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/9af249d2-ac7b-5c82-9b53-495a9f6a0e6e
-- title:
--   Two wide supersingular nodes force two Hasse exponents 2
-- statement:
--   Let $p\ge 13$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ belongs to the nonunits of $A$, and assume its residue field $k=\mathrm{ResidueField}(A)$ has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$ and $\Delta$ an annulus context `AnnCtx` over $\Gamma$, supplying for each of the $\mathrm{mAnnuli}(p)=\lfloor p/12\rfloor+[p\equiv 2\bmod 3]+[p\equiv 3\bmod 4]$ indices $e$ a pair of annuli attached to the charts at $\mathrm{src}(e)$ and $\mathrm{tgt}(e)$, with modulus $p^{\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$. Let $\Phi$ be a family context `FamCtx p r` with members $t_l$, $l\in\mathrm{Fin}\,r$, and write $\mathrm{hasseExp}\,\Phi\,l=(\mathrm{hasseContent}\,\Phi\,l).\mathrm{toNat}$, so that $\mathrm{goodFamilyZero}\,\Phi\,l=p^{-\mathrm{hasseExp}\,\Phi\,l}t_l$. Assume each $\mathrm{goodFamilyZero}\,\Phi\,l$ lies in the integers of the chart $\mathrm{zeroChart}\,\Gamma$, and that the $r$ residues of these elements in that chart are linearly independent over $k$. The conclusion: for all $e_1\ne e_2$ with $\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e_i)\ne 1$, i.e. both supersingular values equal to $0$ or $1728$ (widths $3$ and $2$ respectively), there exist $l_2\ne l_3$ in $\mathrm{Fin}\,r$, both of index $\ge 1$, with $\mathrm{hasseExp}\,\Phi\,l_2=\mathrm{hasseExp}\,\Phi\,l_3=2$.
--
--   This is a counting step in the analysis of the two-component multiplicative covering of $X_0(p)$ with its supersingular annuli: the presence of two wide supersingular nodes, which happens exactly when both $j=0$ and $j=1728$ are supersingular, produces two distinct members of positive index in the good family whose Hasse exponent attains the maximal value $2$ permitted for $p\ge 13$. It feeds the cross-comparison of two annuli in [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_ne_hasseExp_eq_two_of_jWidth_ne_one.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_ne_hasseExp_eq_two_of_jWidth_ne_one (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩)) :
    ∀ e₁ e₂ : Fin (mAnnuli p), e₁ ≠ e₂ → jWidth (ssValue Γ e₁) ≠ 1 → jWidth (ssValue Γ e₂) ≠ 1 →
      ∃ l₂ l₃ : Fin r, l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
        hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 2 := by sorry
