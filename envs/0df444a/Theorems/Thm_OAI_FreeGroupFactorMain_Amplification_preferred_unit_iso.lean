-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_preferred_unit_iso
-- name    : OAI.FreeGroupFactorMain.Amplification.preferred_unit_iso
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T03:01:48.033596+00:00
-- url     : https://prove2.me/theorems/c1977bc1-f643-430f-8dd5-4de14c379c40
-- title:
--   A unit-trace corner of the stabilization is the original factor
-- statement:
--   Let $G$ be a group with every central element of $L(G)$ a scalar. Let $p$ be a projection of the stabilization $\mathcal S(G)$ with trace $1$. Then $p\mathcal S(G)p$ with normalized corner trace and induced ultraweak topology is isomorphic to $L(G)$ by a trace-preserving $*$-isomorphism continuous in both directions:
--
--   $$p\,\mathcal S(G)\,p\cong L(G).$$
--
--   This records $Q^1\cong Q$ in the amplification convention of Section 6 of the paper.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Amplification.preferred_unit_iso`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/NormalEquiv.lean#L87

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

theorem preferred_unit_iso
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (p : stabilization G) (hp : IsStarProjection p) (hptr : stabilizedProjectionTrace p=ENNReal.ofReal 1) :
    Nonempty (GroupCornerNormalIso 1 p hp) := by
  sorry

end FreeGroupFactorMain.Amplification
end
end OAI
