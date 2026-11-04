-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_preferred_scaling_model
-- name    : OAI.FreeGroupFactorMain.Amplification.preferred_scaling_model
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T02:56:58.724974+00:00
-- url     : https://prove2.me/theorems/26787821-6308-496f-80d5-2db06100f664
-- title:
--   Corner scaling for small parameters gives all amplifications
-- statement:
--   Let $G$ be a group with every central element of $L(G)$ a scalar. Suppose that for every $t\in(0,1]$, $L(G)$ has corner scaling at $t$: there is a projection $p$ of trace $t$ and a trace-scaling, ultraweakly bicontinuous $*$-isomorphism $L(G)\to pL(G)p$. Then for every $t>0$ there is a projection $p$ in the stabilization $\mathcal S(G)$ with trace $t$ and a normal isomorphism
--
--   $$p\,\mathcal S(G)\,p\cong L(G)$$
--
--   which carries the normalized corner trace to the canonical trace.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0); Lean declaration `OAI.FreeGroupFactorMain.Amplification.preferred_scaling_model`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/InterpolatedFactors/Positive.lean#L20

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

theorem preferred_scaling_model
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (t : ℝ) (ht : 0<t) :
    ∃ (p : stabilization G) (hp : IsStarProjection p),
      stabilizedProjectionTrace p=ENNReal.ofReal t ∧ Nonempty (GroupCornerNormalIso t p hp) := by
  sorry

end FreeGroupFactorMain.Amplification
end
end OAI
