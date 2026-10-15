-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_projectionLaw_set_bound
-- name    : OAI.NoiselessRegression.projectionLaw_set_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:30:22.812386+00:00
-- url     : https://prove2.me/theorems/1de310c2-02e7-47f3-86c4-55d872e35d62
-- title:
--   Hölder-type absolute continuity of the noiseless Gaussian projection law
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d$ with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $\lambda_m$ be Lebesgue measure on $\mathbb R^m$. On $E^m\times\mathbb R^m$ consider the reference measure $R_m=\gamma_E^{\otimes m}\otimes\lambda_m$ and, for a finite Borel measure $\nu$ on $E$, the noiseless projection law $P_{\nu,m}$, defined as the image of $\gamma_E^{\otimes m}\otimes\nu$ under the map $(A,t)\mapsto\big(A,(\langle t,A_1\rangle,\dots,\langle t,A_m\rangle)\big)$. Thus $P_{\nu,m}$ is the joint law of a Gaussian design $A=(A_1,\dots,A_m)$ and the exact labels $\langle t,A_j\rangle$ of a parameter $t$ drawn from $\nu$.
--
--   Assume that $\nu$ is finite, that its support lies in the closed unit ball $\bar B(0,1)$, and that it satisfies a local mass bound with exponent $a\in\mathbb R$: $\nu\big(\bar B(t,r)\big)\le r^{a}$ for all $t\in\operatorname{supp}\nu$ and $r>0$. Let $K_{\nu,a,m}=\nu(E)+3^{d}4^{a}2^{m+1}$. If $m,n\in\mathbb N$ satisfy $n\ge1$ and $n+m\le a$, then for every set $S\subseteq E^m\times\mathbb R^m$,
--
--   $$
--   P_{\nu,m}(S)\;\le\;\big(\nu(E)\,K_{\nu,a,m}^{\,n}\big)^{1/(n+1)}\,R_m(S)^{1-1/(n+1)}.
--   $$
--
--   Although the labels are deterministic functions of $(A,t)$, the observation law is absolutely continuous with respect to $R_m$, with a quantitative Hölder modulus of exponent $n/(n+1)$; in particular $P_{\nu,m}(S)=0$ whenever $R_m(S)=0$. Combined with a set of finite reference measure that contains all noiseless observations, this bounds how much probability the observations can place on any given set of designs and labels.
--
--   **Formalization Note** The set $S$ need not be measurable; for non-measurable sets both sides are evaluated with the outer measures that Mathlib's measures carry. All quantities lie in $[0,\infty]$, $P_{\nu,m}$ is `projectionLaw ν m`, $R_m$ is `matrixLabelReference m`, and $K_{\nu,a,m}$ is `replicaConstant ν a m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Projection.lean#L98-L134

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.projectionLaw_set_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hn : 1 ≤ n) (hmargin : (n : ℝ) + m ≤ a)
    (S : Set ((Fin m → E) × (Fin m → ℝ))) :
    projectionLaw ν m S ≤
      (ν Set.univ * (replicaConstant ν a m)^n)^(1 / ((n : ℝ) + 1)) *
      (matrixLabelReference (E := E) m S)^(1 - 1 / ((n : ℝ) + 1)) := by sorry
