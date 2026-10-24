-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2_part3
-- name    : MaintPOMDP.Frontier.theorem_2_part3
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-24T02:04:41.48392+00:00
-- url     : https://prove2.me/theorems/e8807df2-c85c-4463-9ba8-8425b17533fc
-- title:
--   Theorem 2(3), pp. 27–28 — [PR], I[PR], [PIR] with thresholds $0<\hat c_1\le\hat c_2<c^R$
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$, and let $\mathbf u^{(\dot P)}=(u_0^{(\dot P)},u_1^{(\dot P)})'$, $u_F^{(\dot P)}=u_0^{(\dot P)}+c^F$ be the continuation cost of producing forever (23)–(24). Let $f$ and $g$ be the solutions of the anchor equations of Lemmas 3 and 7.
--
--   **Theorem 2 (3), recurrent replacement.** If $c^R<\min\{\frac{\gamma_0}{\gamma_1}\theta,\theta\}$, let $m^\dagger$ be the least minimizer of $f$ over $\{0,1,\dots\}$ and $(U^\dagger,u^\dagger_F)$ the $[PR]$ frontier of Theorem 1 ($U^\dagger=\{\mathbf u_0,\dots,\mathbf u_{m^\dagger+1}\}$ from $\mathbf u_0=(f(m^\dagger),f(m^\dagger))'$, $u^\dagger_F=f(m^\dagger)+c^F-c^R$). Then there are thresholds $0<\hat c_1\le\hat c_2<c^R$, depending only on the parameters other than $c^I$, such that for every inspection cost $c^I\in(c^P,c^R)$:
--   - if $c^I\ge\hat c_2$: structure $[PR]$, the optimal solution of $\{P,I,R\}$ is $(U^\dagger,u^\dagger_F)$;
--   - if $\hat c_1\le c^I<\hat c_2$: structure $I[PR]$, the optimal solution is $(U^\dagger\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\},u^\dagger_F)$ for some $n_I$, with $\mathbf u^I_0=\mathbf u^{I\dagger}=(u^\dagger_0-c^R+c^I,\ c^I+\beta\gamma_1(c^F-c^R)+\beta u^\dagger_0)'$ and the sequence following (37);
--   - if $c^I<\hat c_1$: structure $[PIR]$ as in Theorem 2 (2).
--
--   Moreover, at $c^I=\hat c_2$ the point $\mathbf u^{I\dagger}$ lies on the efficient frontier of $U^\dagger$, and at $c^I=\hat c_1$ one has $\min_m f(m)=\min_m g(m)$ (stated with minimizers).
--
--   Here \"$(U,u_F)$ is the optimal solution of the $\{P,I,R\}$ model\" means that the dual value iteration (12)–(16) with actions $\{P,I,R\}$, started from zero terminal costs, converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every unnormalized belief $\boldsymbol\pi\ge0$, and its failure coordinate converges to $u_F$.
--
--   This is the third conjunct of Theorem 2, stated separately and verbatim from the parent formalization.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (3) (pp. 27–28; Table 1, rows [PR], I[PR], [PIR]): if c^R < min{(γ0/γ1)·thrP, thrP},
there are thresholds 0 < ĉ1 ≤ ĉ2 < c^R, independent of c^I, separating the three structures for every
inspection cost c ∈ (c^P, c^R), with their implicit characterizations. -/
theorem theorem_2_part3 (M : Params) (hM : M.Standing)
    (hcR : M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP) :
    ∃ mdag : ℕ, IsLeastMin M.f mdag ∧
      ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ c2 < M.cR ∧
        (∀ c : ℝ, M.cP < c → c < M.cR →
          (c2 ≤ c →
            (M.withCI c).Solves ActSet.PIR ((M.withCI c).Udag mdag)
              ((M.withCI c).f mdag + M.cF - M.cR)) ∧
          (c1 ≤ c → c < c2 →
            ∃ nI : ℕ, (M.withCI c).Solves ActSet.PIR ((M.withCI c).UIPR mdag nI)
              ((M.withCI c).f mdag + M.cF - M.cR)) ∧
          (c < c1 → (M.withCI c).PIRStructure)) ∧
        OnFrontier ((M.withCI c2).uIdag ((M.withCI c2).f mdag)) ((M.withCI c2).Udag mdag) ∧
        ∃ m1 m2 : ℕ, (∀ m, M.f m1 ≤ M.f m) ∧ (∀ m, (M.withCI c1).g m2 ≤ (M.withCI c1).g m) ∧
          M.f m1 = (M.withCI c1).g m2 := by sorry

end MaintPOMDP.Frontier
