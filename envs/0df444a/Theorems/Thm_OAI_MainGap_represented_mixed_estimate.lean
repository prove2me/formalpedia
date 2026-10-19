-- Prove2me | Theorems.Thm_OAI_MainGap_represented_mixed_estimate
-- name    : OAI.MainGap.represented_mixed_estimate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:25:51.665976+00:00
-- url     : https://prove2.me/theorems/4cc648af-ca7a-4f41-b425-e57acd399b7e
-- title:
--   Norm bound for $\pi(UwV)$ from a small first sandwich in a representation
-- statement:
--   Let $A$ and $\mathcal{D}$ be unital C*-algebras with their usual orders, and let $\pi:A\to\mathcal{D}$ be a unital $*$-homomorphism. For self-adjoint $U$ and $\eta\in\mathbb{R}$ let $(U-\eta)_+$ be $\max(t-\eta,0)$ applied to $U$ by continuous functional calculus. For $U,V\in A$, $\eta\in\mathbb{R}$ and a finite set $E\subseteq A$ define the *first sandwich*
--
--   $$
--   \Theta(U,V,\eta,E)=(U-\eta)_+\Big(\sum_{w'\in E}w'\,V\,w'^{*}\Big)(U-\eta)_+.
--   $$
--
--   **Theorem.** Let $U,V\in A$ be positive, $\eta>0$, $E\subseteq A$ finite and $w\in E$. If $\|\pi(\Theta(U,V,\eta,E))\|\le2\eta$, then
--
--   $$
--   \|\pi(UwV)\|\le\sqrt{2\eta}\,\big\|V^{1/2}\big\|+\eta\,\|w\|\,\|V\|.
--   $$
--
--   Thus smallness of one positive element built from a finite test set $E$ controls all mixed products $UwV$ with $w\in E$ in the representation, up to an error proportional to $\eta$. Letting $E$ grow and $\eta$ shrink along an index set, this makes $\pi_i(UwV)$ tend to zero for every fixed $w$.
--
--   **Formalization Note** $\Theta$ is `firstSandwich U V η E`, $V^{1/2}$ is `CFC.sqrt V`, and $\pi$ is a unital star-algebra homomorphism `A →⋆ₐ[ℂ] D`. Both algebras carry `CStarAlgebra.spectralOrder`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/CStarAlgebra/PureInfiniteness/Defect.lean#L246-L269

import Mathlib
import Definitions.Def_IndividualStrongInfiniteness
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ClosedIdeal
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_PositiveFunctional
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Representation
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Hereditary
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Comparison
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_OrthogonalSlots
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Cutoffs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_ChoicePairs
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_FourChoices
import Definitions.Def_OAI_Analysis_CStarAlgebra_PureInfiniteness_Defect

open OAI OAI.MainGap
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace
attribute [local instance] OAI.MainGap.defectSandwichOrder
attribute [local instance] OAI.MainGap.defectSandwichStarOrder
attribute [local instance] OAI.MainGap.representedDefectOrder
attribute [local instance] OAI.MainGap.representedDefectStarOrder
variable {A D : Type*} [CStarAlgebra A] [CStarAlgebra D]

theorem OAI.MainGap.represented_mixed_estimate (π : A →⋆ₐ[ℂ] D) {U V w : A} (hU : 0 ≤ U) (hV : 0 ≤ V)
    {η : ℝ} (hη : 0 < η) {E : Finset A} (hw : w ∈ E)
    (hD : ‖π (firstSandwich U V η E)‖ ≤ 2*η) :
    ‖π (U*w*V)‖ ≤ Real.sqrt (2*η) * ‖CFC.sqrt V‖ + η*‖w‖*‖V‖ := by sorry
