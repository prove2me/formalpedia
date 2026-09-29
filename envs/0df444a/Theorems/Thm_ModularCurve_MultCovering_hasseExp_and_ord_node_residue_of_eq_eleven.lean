-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven
-- name    : ModularCurve.MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/97e6b842-5ce8-537c-be24-a1da65dc3a06
-- title:
--   Hasse exponents and node orders for p = 11
-- statement:
--   Let $p$ be a prime with $p = 11$, let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ (that is, the image of $p$ lies in the non-units of $A$), with residue field of characteristic $p$; let $\Gamma$ be a chart context for $p$ and $A$ and $\Delta$ an annulus context over $\Gamma$, and let $\Phi$ be a family context with three members $t_0,t_1,t_2$ in the function field $\overline{F}(1\cdot p)$. Assume that each rescaled member $\mathrm{goodFamilyZero}(\Phi,l) = (p^{\,\mathrm{hasseExp}(\Phi,l)})^{-1} t_l$ is integral for the zero chart $\mathrm{zeroChart}\,\Gamma$ (the pullback of the infinity chart along the Fricke involution), and that the three resulting residues are linearly independent over the residue field of $A$. Assume finally that $\mu$ is a real absolute value on $\overline{\mathbb Q}$ whose unit ball is exactly $A$. Then each $t_l$ is integral for $\mathrm{infChart}\,\Gamma$, and there are distinct indices $l_2,l_3 \in \mathrm{Fin}\,3$, both $\ge 1$, with Hasse exponents $\mathrm{hasseExp}(\Phi,l_2) = 2$ and $\mathrm{hasseExp}(\Phi,l_3) = 3$, such that for every annulus index $e$ (there are $\mathrm{mAnnuli}\,p = p/12 + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ of them, hence two for $p = 11$): if the supersingular value $\mathrm{ssValue}\,\Gamma\,e$ equals $1728$, then the residue of $t_{l_2}$ on the infinity chart has order $1$ at the target node $\mathrm{nodeTgt}\,\Gamma\,e$ (the geometric place at $\mathrm{ssValue}\,\Gamma\,e$), the residue of $p^{-2} t_{l_2}$ on the zero chart has order $-1$ at the source node $\mathrm{nodeSrc}\,\Gamma\,e$ (the geometric place at $(\mathrm{ssValue}\,\Gamma\,e)^p$), and the residue of $t_{l_3}$ has order $2$ at the target node; and if $\mathrm{ssValue}\,\Gamma\,e = 0$, then the residue of $t_{l_3}$ has order $1$ at the target node and the residue of $p^{-3} t_{l_3}$ has order $-1$ at the source node.
--
--   This is the numerical certificate for the prime $p = 11$, where the two supersingular $j$-invariants in characteristic $11$ are $0$ and $1728$ with tube widths $3$ and $2$: it pins down the Hasse exponents of two members of the good family and their orders of vanishing and poles at the supersingular nodes of the two components of the degenerate fibre. It feeds the cross-comparison of the inner annuli with the zero chart, the construction of unimodular family data with wide certificates for $p = 11$, and thereby the uniform multiplicative covering with a certified family for all primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_and_ord_node_residue_of_eq_eleven.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseExp_and_ord_node_residue_of_eq_eleven (p : ℕ) [Fact p.Prime] (hp11 : p = 11)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (Φ : FamCtx p 3)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin 3 => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (l₂ l₃ : Fin 3),
      l₂ ≠ l₃ ∧ 1 ≤ (l₂ : ℕ) ∧ 1 ≤ (l₃ : ℕ) ∧
      hasseExp Φ.toFamData l₂ = 2 ∧ hasseExp Φ.toFamData l₃ = 3 ∧
      ∀ e : Fin (mAnnuli p),
        (ssValue Γ e = 1728 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₂, hint l₂⟩) = -1 ∧
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 2) ∧
        (ssValue Γ e = 0 →
          (nodeTgt Γ e).ord ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩) = 1 ∧
          (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l₃, hint l₃⟩) = -1) := by sorry
