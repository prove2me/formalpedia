-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_lhs12_monotone
-- name    : InfoNudge.Cutoff.lhs12_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:54.149494+00:00
-- url     : https://prove2.me/theorems/94fdec12-93e6-42cf-a602-6d9871b91c24
-- title:
--   Proof of Proposition 2, p. 16 — the left-hand side of (12) increases continuously from E[θ] to θ̄ as γ goes from 0 to 1, strictly below θ̄
-- statement:
--   Under the standing assumptions, for $\gamma\in[0,1)$ let
--   $$A(\gamma)=\frac{E[\theta(1-\pi^*_\gamma(\theta))]}{1-\gamma}$$
--   be the left-hand side of (12), the mean type among those recommended to abstain by the cutoff mechanism $\pi^*_\gamma$, and let $\bar\theta$ be the supremum of the support of $P$. Then
--
--   1. $A(0)=E[\theta]$;
--   2. $A$ is continuous and nondecreasing on $[0,1)$;
--   3. $A$ is strictly increasing on the set of $\gamma\in[0,1)$ with $A(\gamma)<\bar\theta$;
--   4. $A(\gamma)\to\bar\theta$ as $\gamma\uparrow1$.
--
--   This is the first observation in the proof of Proposition 2: it yields a unique $\gamma^c$ at which (12) holds with equality.
--
--   **Formalization Note** The paper says that $A$ "strictly and continuously increases from $E[\theta]$ to $\bar\theta$". If $P$ has an atom at $\bar\theta$, then $A\equiv\bar\theta$ on $[1-P\{\bar\theta\},1)$, so strictness holds only where $A<\bar\theta$; the statement is corrected accordingly. This is all the proof of Proposition 2 uses, since there $t^a<\bar\theta$.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 16, proof of Proposition 2, left-hand side of (12)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

open Filter Topology

theorem lhs12_monotone (M : Params) (hS : Standing M) :
    abstainMean M 0 = (∫ θ, θ ∂M.P) ∧
    ContinuousOn (abstainMean M) (Set.Ico 0 1) ∧
    MonotoneOn (abstainMean M) (Set.Ico 0 1) ∧
    StrictMonoOn (abstainMean M) {γ ∈ Set.Ico (0 : ℝ) 1 | abstainMean M γ < thetaBar M} ∧
    Tendsto (abstainMean M) (𝓝[<] 1) (𝓝 (thetaBar M)) := by sorry

end InfoNudge.Cutoff
