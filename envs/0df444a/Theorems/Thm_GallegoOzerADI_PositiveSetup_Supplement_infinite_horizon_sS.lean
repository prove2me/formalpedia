-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_Supplement_infinite_horizon_sS
-- name    : GallegoOzerADI.PositiveSetup.Supplement.infinite_horizon_sS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:42:01.705565+00:00
-- url     : https://prove2.me/theorems/d5d420ee-6910-43d4-bb20-6cfa688ef125
-- title:
--   Theorem 3 (corrected: uniform convergence on every half-line $(-\infty,B]$) — infinite-horizon state-dependent $(s,S)$ policy and myopic threshold
-- statement:
--   Consider the stationary inventory problem with advance demand information and positive set-up cost: lead time $L\ge0$, $M\ge1$ observed demands beyond the protection period, single-period cost $G$ convex with $G(y)\to\infty$ as $|y|\to\infty$, set-up cost $K>0$, discount factor $0<\alpha<1$, and i.i.d. demand vectors with law $\mu$, a probability measure with nonnegative components. Let $J_n$, $V_n$ be the optimal cost and cost-to-go with $n$ further periods, $S_n(o)$ the smallest minimizer of $V_n(\cdot,o)$ and $s_n(o)=\max\{y:H_n(y,o)\le0\}$; letting $T\to\infty$ with $t$ fixed is letting $n\to\infty$. For a function $J$ write
--   $$
--   V(y,o)=G(y)+\alpha\,\mathbb E\Big\{J\Big(y-D_{t,t}-\sum_{s=t+1}^{t+L+1}D_{t,s}-o_{t,t+L+1},\,O_{t+1}\Big)\Big\},\qquad H(y,o)=K+\min_{z\ge y}V(z,o)-V(y,o).
--   $$
--   Then there are a function $J(x,o)$ and functions $s(o)$, $S(o)$ such that, for every observed-demand vector $o\ge0$:
--
--   1. for every $B\in\mathbb R$, $J_n(\cdot,o)\to J(\cdot,o)$ uniformly on $(-\infty,B]$; $J$ satisfies the functional equation (8), $J(x,o)=\min_{y\ge x}\{K\delta(y-x)+V(y,o)\}$; and $J(x,o)$ is the optimal value of the infinite-horizon problem from $(x,o)$ for every $x$;
--   2. $s_n(o)\to s(o)$ and $S_n(o)\to S(o)$; every limit point of $(S_n(o))_n$ minimizes $V(\cdot,o)$; $V(\cdot,o)$ is $(0,K)$-convex; and $s(o)=\max\{y:H(y,o)\le0\}$;
--   3. the state-dependent policy that orders up to $S(o)$ when $x\le s(o)$ and does not order otherwise is admissible and optimal for the infinite-horizon problem from every state $(x,o)$;
--   4. if $o_{t,t+L+1}\ge\overline S-s^m$, then $S(o)=S^m$, where $S^m$ is the smallest minimizer of $G$, $s^m=\max\{y\le S^m:G(y)\ge K+G(S^m)\}$ and $\overline S=\inf\{y>S^m:G(y)>G(S^m)+\alpha K\}$.
--
--   The infinite-horizon problem minimizes $\mathbb E\sum_{k\ge0}\alpha^k\{K\delta(y_k-x_k)+G(y_k)\}$ over all admissible policies, including history-dependent ones. Part 4 extends the finite-horizon Theorem 2, the goal of this mission, to the infinite horizon.
--
--   **Formalization Note.** No sign, growth or moment condition is placed on $G$; $o$ ranges over the reachable nonnegative observation vectors. The functions $s,S$ are given for all $o$; only their values at $o\ge0$ are constrained, apart from the admissibility of the policy. The expected discounted cost is $\mathbb E[\sum(\alpha^kc_k)^+]-\mathbb E[\sum(\alpha^kc_k)^-]$ in the extended reals.
--
--   Differences from the source:
--   - correction: J_t(·,o) converges uniformly (on the whole inventory line) → uniformly on every half-line (−∞, B]; reason: the printed claim is false: with L = 0, N = 2, deterministic D = (1,0,0), o = 0, G(y) = |y − 1|, any K > 0, α = 1/2, one has J − J_n ≥ α^n(x − n − 1) for x ≥ n + 1, so the supremum over x is infinite for every n (DISPROOF.md); the proof on p. 1357 only bounds J by a quantity C_M depending on the initial inventory
--   - reading: the infinite-horizon problem with an unstated discount range → 0 < α < 1; reason: the proof on p. 1357 divides by 1 − α; the infinite-horizon problems are discounted
--   - reading: the optimal value function of the infinite-horizon problem → the infimum, over admissible measurable non-anticipative deterministic history-dependent policies, of E[Σ(α^k c_k)^+] − E[Σ(α^k c_k)^−] with c_k = Kδ(y_k − x_k) + G(y_k) and i.i.d. demand vectors; reason: Eq. (12) of Appendix A with T = ∞; randomized policies are not in the class
--   - reading: the policy (s(o), S(o)) is optimal → the stationary policy ordering up to S(o_k) iff x_k ≤ s(o_k) is admissible and attains the optimal value from every (x, o) with o ≥ 0; reason: the (s, S) policy of Corollary 1 is state dependent
--   - reading: for any fixed vector o, with the paper's J_t, V_t, s_t, S_t of a horizon-T problem → for every o ≥ 0, with J_n, V_n, s_n, S_n of n further periods and n → ∞; reason: stationary values depend only on T − t (p. 1351); observed demands are nonnegative on reachable states
--   - encoding: S̄ printed as min{y > S^m : G(y) > G(S^m) + αK} → the infimum of that set; reason: inherited from the published MyopicLevels definition used by the goal; the set is open for continuous G and has no minimum
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 3; proof p. 1357

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary
import Definitions.Def_GallegoOzerADI_PositiveSetup_ABConvex
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup.Supplement

/-- Theorem 3 (p. 1351), stationary positive set-up cost, infinite horizon, with the global
uniform convergence of Part 1 corrected to uniform convergence on every half-line `(-∞, B]`
(see the item's Differences from the source). -/
theorem infinite_horizon_sS {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (K α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hK : 0 < K) (hα₀ : 0 < α) (hα₁ : α < 1)
    (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∃ (J : ℝ → (Fin M → ℝ) → ℝ) (s S : (Fin M → ℝ) → ℝ),
      -- Part 1: convergence, the functional equation (8), and optimality of the limit
      (∀ o : Fin M → ℝ, 0 ≤ o →
        (∀ B : ℝ, TendstoUniformlyOn (fun n x => Jgo G K α μ n x o) (fun x => J x o) atTop
          (Set.Iic B)) ∧
        (∀ x, J x o = orderCost K (fun y => contValue G α μ J y o) x) ∧
        (∀ x, infValue G K α μ x o = (J x o : EReal))) ∧
      -- Part 2: convergence of the policy parameters and structure of the limit
      (∀ o : Fin M → ℝ, 0 ≤ o →
        Tendsto (fun n => reorderLevel G K α μ n o) atTop (𝓝 (s o)) ∧
        Tendsto (fun n => orderUpToLevel G K α μ n o) atTop (𝓝 (S o)) ∧
        (∀ z, MapClusterPt z atTop (fun n => orderUpToLevel G K α μ n o) →
          ∀ y, contValue G α μ J z o ≤ contValue G α μ J y o) ∧
        ABConvex 0 K (fun y => contValue G α μ J y o) ∧
        IsGreatest {y | reorderGap K (fun z => contValue G α μ J z o) y ≤ 0} (s o)) ∧
      -- Part 3: the state-dependent (s, S) policy is optimal for the infinite-horizon problem
      (∀ (x : ℝ) (o : Fin M → ℝ), 0 ≤ o →
        (adiSystem (L := L) G K).IsOptimalFrom α μ (sSPolicy s S) (x, o)) ∧
      -- Part 4: the myopic order-up-to level is optimal beyond the threshold
      (∀ o : Fin M → ℝ, 0 ≤ o →
        myopicUpperLevel G K α - myopicReorderPoint G K ≤ o 0 → S o = myopicOrderUpTo G) := by
  sorry

end GallegoOzerADI.PositiveSetup.Supplement
