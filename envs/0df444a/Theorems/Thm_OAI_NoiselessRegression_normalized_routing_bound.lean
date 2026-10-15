-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_normalized_routing_bound
-- name    : OAI.NoiselessRegression.normalized_routing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:31:11.761431+00:00
-- url     : https://prove2.me/theorems/8d41799c-a1b2-44db-8d80-5c98a800898c
-- title:
--   Routing bound for finitely many projection laws with local mass bounds
-- statement:
--   Let $E$ be a real inner product space of finite dimension $d\ge1$ with its Borel $\sigma$-algebra and standard Gaussian measure $\gamma_E$, and let $\lambda_m$ be Lebesgue measure on $\mathbb R^m$. For a finite Borel measure $\nu$ on $E$, let $P_{\nu,m}$ be the noiseless projection law on $E^m\times\mathbb R^m$, defined as the image of $\gamma_E^{\otimes m}\otimes\nu$ under $(A,t)\mapsto\big(A,(\langle t,A_1\rangle,\dots,\langle t,A_m\rangle)\big)$.
--
--   Let $J$ be a finite set with a $\sigma$-algebra in which singletons are measurable, and let $(\nu_j)_{j\in J}$ be finite Borel measures on $E$. Let $a,m,n\in\mathbb N$ and assume:
--
--   1. each $\nu_j$ has total mass $\nu_j(E)\le1$, support in the closed unit ball $\bar B(0,1)$, and the local mass bound $\nu_j\big(\bar B(t,r)\big)\le r^{a}$ for all $t\in\operatorname{supp}\nu_j$ and $r>0$;
--   2. $a\le d$, $m\le d$, $n\ge1$ and $n+m\le a$.
--
--   Then every measurable map $\phi:E^m\times\mathbb R^m\to J$ satisfies
--
--   $$
--   \sum_{j\in J}P_{\nu_j,m}\big(\{x:\phi(x)=j\}\big)\;\le\;32768^{d}\,|J|^{1/(n+1)}.
--   $$
--
--   Think of $\phi$ as a rule that reads one block of $m$ noiseless observations and outputs an index in $J$, and of $\nu_j$ as the distribution of the parameter in hypothesis $j$. The sum adds up the mass that each hypothesis sends to its own index, and is trivially at most $|J|$. The theorem bounds it by $32768^d|J|^{1/(n+1)}$, so the average over $j$ of the correctly routed mass is at most $32768^d|J|^{-n/(n+1)}$, which is small as soon as $|J|$ is large compared with $32768^{d(n+1)/n}$.
--
--   **Formalization Note** The constant is $32768=2^{15}=128\cdot256$. The exponent $a$ is a natural number here, and $|J|$ is `Fintype.card J`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Blocks.lean#L149-L206

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
import Definitions.Def_OAI_Probability_GaussianRegression_Projection
import Definitions.Def_OAI_Probability_GaussianRegression_Support
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.NoiselessRegression.normalized_routing_bound {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] (ν : J → Measure E) [∀ j, IsFiniteMeasure (ν j)]
    {a m n : ℕ} (hν : ∀ j, HasLocalMassBound (ν j) (a : ℝ))
    (hν1 : ∀ j, ν j univ ≤ 1) (hsupport : ∀ j, (ν j).support ⊆ Metric.closedBall 0 1)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hm : m ≤ Module.finrank ℝ E) (hn : 1 ≤ n) (hmargin : n+m ≤ a)
    (φ : ((Fin m → E) × (Fin m → ℝ)) → J) (hφ : Measurable φ) :
    (∑ j, projectionLaw (ν j) m {x | φ x = j}) ≤
      (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/((n : ℝ)+1)) := by sorry
