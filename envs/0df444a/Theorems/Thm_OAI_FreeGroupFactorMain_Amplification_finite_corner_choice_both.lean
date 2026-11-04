-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_finite_corner_choice_both
-- name    : OAI.FreeGroupFactorMain.Amplification.finite_corner_choice_both
-- status  : Open
-- author  : @wurtle
-- created : 2026-11-04T03:06:59.923138+00:00
-- url     : https://prove2.me/theorems/63727e33-59bf-4e81-901e-8536b65071ce
-- title:
--   Equal-trace corners of the stabilization are isomorphic
-- statement:
--   Let $G$ be a group with $L(G)$ a factor, in the sense that every central element of $L(G)$ is a scalar. Let $\mathcal S(G)$ be the stabilization of $L(G)$ acting on $\ell^2(\mathbb N\times G)$, with semifinite trace on projections. Let $t\in\mathbb R$, and let $p,q$ be projections of $\mathcal S(G)$ of the same finite trace. There is a $*$-isomorphism $\Phi:p\mathcal S(G)p\to q\mathcal S(G)q$ with
--
--   $$\tau_{t,q}(\Phi(x))=\tau_{t,p}(x),$$
--
--   where $\tau_{t,p}=t^{-1}\tau|_{p\mathcal S(G)p}$ is the normalized corner trace, and such that $\Phi$ and $\Phi^{-1}$ are continuous for the induced ultraweak topologies.
--
--   This is the independence of the choice of projection in the amplification convention of Section 6 of the paper.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Amplification.finite_corner_choice_both`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/DoubleTrace.lean#L184

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification

section
open scoped ENNReal
variable {G : Type u_1} [Group G]

section Singles
variable [DecidableEq G]

end Singles

end

section
variable {G : Type u_2} [Group G]

end

variable {G : Type u_3} {H : Type u_4} [Group G] [Group H]

theorem finite_corner_choice_both
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (t : ℝ) (p q : stabilization G) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htrace : stabilizedProjectionTrace p=stabilizedProjectionTrace q)
    (hfinite : stabilizedProjectionTrace p ≠ ⊤) :
    ∃ Φ : Corner p hp ≃⋆ₐ[ℂ] Corner q hq,
      (∀ x, normalizedCornerTrace stabilizedTrace t q hq (Φ x)=
        normalizedCornerTrace stabilizedTrace t p hp x) ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) p hp)
        (cornerTopology (stabilizationTopology G) q hq) Φ ∧
      @Continuous _ _ (cornerTopology (stabilizationTopology G) q hq)
        (cornerTopology (stabilizationTopology G) p hp) Φ.symm := by
  sorry

end FreeGroupFactorMain.Amplification
end
end OAI
