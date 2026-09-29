-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two
-- name    : ModularCurve.MultCovering.tangentDet_ne_zero_of_hasseExp_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/8ba68790-5236-5eae-9694-0e976df0b594
-- title:
--   Non-vanishing tangent determinant for two content-2 family members
-- statement:
--   Let $p$ be a prime with $13 \le p$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (so $A$ lies over $p$) and with residue field of characteristic $p$, and let $\Gamma$ be a chart context for $(p,A)$ and $\Delta$ an annulus context over $\Gamma$, providing for each $e \in \mathrm{Fin}(mAnnuli\;p)$ a pair of annuli $\mathrm{An}\,e$, $\mathrm{An}'\,e$ with common domain and modulus $p^{jWidth(ssValue\,\Gamma\,e)}$, whose parameters multiply to the modulus, and which are attached to the source and target charts at the nodes $nodeSrc\,\Gamma\,e$, $nodeTgt\,\Gamma\,e$. Let $\Phi$ be a good-family context of rank $r$ with members $t_l$, and assume that each rescaled member $p^{-hasseExp(\Phi,l)} t_l$ lies in the integers of the zero chart and that the $r$ residues of these elements in the zero chart are linearly independent over the residue field of $A$. Let $e \ne e'$ with $jWidth(ssValue\,\Gamma\,e) \ne 1$ and $jWidth(ssValue\,\Gamma\,e') \ne 1$ (so both supersingular values are $0$ or $1728$), and let $l_2 \ne l_3$ with $hasseExp(\Phi,l_2) = hasseExp(\Phi,l_3) = 2$. The conclusion asserts the existence of proofs that every $t_l$ lies in the integers of the $\infty$-chart and that the parameters of $\mathrm{An}'\,e$ and $\mathrm{An}'\,e'$ do too, such that, writing $w_l(\varepsilon)$ for the value of the place $nodeTgt\,\Gamma\,\varepsilon$ (evaluation via the residue map, with value $0$ off the valuation subring) at the quotient of the $\infty$-chart residue of $t_l$ by that of the parameter of $\mathrm{An}'\,\varepsilon$, one has $w_{l_2}(e)\,w_{l_3}(e') \ne w_{l_3}(e)\,w_{l_2}(e')$ in the residue field of $A$.
--
--   This is the non-degeneracy of the $2 \times 2$ matrix of tangent weights attached to the two wide nodes (supersingular values $0$ and $1728$) and two family members of Hasse exponent $2$; it supplies the determinant hypothesis used by [`ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_annIn_of_orth_of_linearIndependent) in the comparison of incoming annuli in the multiplicative-covering analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.tangentDet_ne_zero_of_hasseExp_two (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (hw : jWidth (ssValue Γ e) ≠ 1) (hw' : jWidth (ssValue Γ e') ≠ 1)
    (l₂ l₃ : Fin r) (h23 : l₂ ≠ l₃) (hn₂ : hasseExp Φ.toFamData l₂ = 2) (hn₃ : hasseExp Φ.toFamData l₃ = 2) :
    ∃ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (hz : (Δ.annOut e).param ∈ (infChart Γ).integers)
      (hz' : (Δ.annOut e').param ∈ (infChart Γ).integers),
      (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)
        ≠ (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹) := by sorry
