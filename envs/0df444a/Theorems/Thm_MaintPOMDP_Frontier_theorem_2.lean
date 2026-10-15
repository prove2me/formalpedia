-- Prove2me | Theorems.Thm_MaintPOMDP_Frontier_theorem_2
-- name    : MaintPOMDP.Frontier.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:27.405771+00:00
-- url     : https://prove2.me/theorems/245b9fac-d577-4a18-ae7c-30aa732a023b
-- title:
--   Theorem 2, pp. 27–28 — under {P, I, R} the optimal solution has one of six structures (Table 1)
-- statement:
--   Under the standing assumptions $0<\beta<1$, $0<c^P<c^I<c^R<c^F$, $0<\gamma_0,\gamma_1<1$, consider the three-action model $\{P,I,R\}$. Write $D=1-\beta+\beta(\gamma_0+\gamma_1)$, $\theta=(c^P+\beta\gamma_1c^F)/D$ and
--   $$\hat c=(1+\beta\gamma_0)c^P-\beta\bar\gamma_1(1-\beta+\beta\gamma_0+\beta\gamma_1)c^R+\beta^2\gamma_1\bar\gamma_1c^F .$$
--   The optimal solution $(U^*,u^*_F)$ is given by Table 1:
--   1. If $c^R\ge\theta$: structure $[P]$, $(U^*,u^*_F)=(\{\mathbf u^{(\dot P)}\},u_F^{(\dot P)})$.
--   2. If $\frac{\gamma_0}{\gamma_1}\theta\le c^R<\theta$:
--      - if $c^I\ge\frac{c^R}{c^P+\beta\gamma_1c^F}\hat c$: structure $R[P]$, $(\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)}\},u_F^{(\dot P)})$;
--      - if $\frac{\gamma_0}{\gamma_1}\frac1D\hat c\le c^I<\frac{c^R}{c^P+\beta\gamma_1c^F}\hat c$: structure $IR[P]$, $(\{\mathbf u^{(\dot P)},\mathbf u^{(R\dot P)},\mathbf u^I\},u_F^{(\dot P)})$ with $\mathbf u^I=\big(c^I+u_0^{(\dot P)},\ c^I+\beta\bar\gamma_1(c^R+u_0^{(\dot P)})+\beta\gamma_1(c^F+u_0^{(\dot P)})\big)'$;
--      - if $c^I<\frac{\gamma_0}{\gamma_1}\frac1D\hat c$: structure $[PIR]$: for some minimizer $m^*$ of $g$ over $\{0,1,\dots\}$ and some $n_R,n_I$, $U^*=\{\mathbf u^R_0,\dots,\mathbf u^R_{n_R}\}\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\}$ with $u^R_0=g(m^*)$, $u^*_F=u^R_0+c^F-c^R$, $\mathbf u^I_0$ by (35) and both sequences by (36)–(37).
--   3. If $c^R<\min\{\frac{\gamma_0}{\gamma_1}\theta,\theta\}$: let $m^\dagger$ be the least minimizer of $f$ and $U^\dagger$ the $[PR]$ frontier of Theorem 1. There exist thresholds $0<\hat c_1\le\hat c_2<c^R$, depending only on the parameters other than $c^I$, such that for every $c^I\in(c^P,c^R)$:
--      - if $c^I\ge\hat c_2$: structure $[PR]$, $(U^\dagger,u^\dagger_F)$ with $u^\dagger_F=f(m^\dagger)+c^F-c^R$;
--      - if $\hat c_1\le c^I<\hat c_2$: structure $I[PR]$, $(U^\dagger\cup\{\mathbf u^I_0,\dots,\mathbf u^I_{n_I}\},u^\dagger_F)$ for some $n_I$, where $\mathbf u^I_0=\mathbf u^{I\dagger}=(u^\dagger_0-c^R+c^I,\ c^I+\beta\gamma_1(c^F-c^R)+\beta u^\dagger_0)'$ and the sequence follows (37) with $u^\dagger_F$;
--      - if $c^I<\hat c_1$: structure $[PIR]$ as in part 2.
--
--      The thresholds are determined implicitly: at $c^I=\hat c_2$, $\mathbf u^{I\dagger}$ lies on the frontier corresponding to $U^\dagger$; at $c^I=\hat c_1$, $\min_{m}f(m)=\min_m g(m)$.
--
--   "$(U,u_F)$ is the optimal solution" means that value iteration for $\{P,I,R\}$ from zero terminal costs converges to $\min_{\mathbf u\in U}\boldsymbol\pi'\mathbf u$ for every belief $\boldsymbol\pi\ge0$ and to $u_F$ after a failure. The theorem is the paper's main result: a complete closed-form description of the optimal maintenance policy.
--
--   **Formalization Note** The theorem is stated at the value level: it does not assert that every listed point of the $I[PR]$ and $[PIR]$ rows is an extreme point, and the "smallest" indices $n_R,n_I$ of Table 1 become existential. Table 1's $I[PR]$ row conflicts with the paper's Proposition 8 on which points are extreme, which is why exactness is not asserted. The ranges $0<\gamma_0,\gamma_1<1$ are added. $f$ and $g$ are the solutions of the anchor equations of Lemmas 3 and 7, valid also for $\gamma_0=\gamma_1$. In part 3 the thresholds are chosen before the inspection cost, and the structure claims are quantified over every inspection cost in $(c^P,c^R)$; "$\min f=\min g$" is stated with minimizers, which exist.
-- source:
--   Zhang, Zhang, Analytical Solution to a Partially Observable Machine Maintenance Problem with Obvious Failures, SSRN 2945049 (version of 2022-08-21), pp. 27–28, Theorem 2; p. 29, Table 1; (34)–(37), p. 26; proof EC pp. 16–20

import Mathlib
import Definitions.Def_MaintPOMDP_Frontier_Setting
open Filter Topology

namespace MaintPOMDP.Frontier

/-- Theorem 2 (pp. 27–28) with Table 1 (p. 29): under actions {P, I, R} the optimal solution has
one of six structures [P], R[P], IR[P], [PIR], [PR], I[PR], determined by thresholds on c^R and c^I.
Part (3) asserts two thresholds 0 < ĉ1 ≤ ĉ2 < c^R, independent of c^I, valid for every inspection
cost c ∈ (c^P, c^R), together with their implicit characterizations. -/
theorem theorem_2 (M : Params) (hM : M.Standing) :
    -- (1) [P]
    (M.thrP ≤ M.cR → M.Solves ActSet.PIR {M.uPdot} M.uFPdot) ∧
    -- (2) R[P], IR[P], [PIR]
    (M.γ0 / M.γ1 * M.thrP ≤ M.cR → M.cR < M.thrP →
      (M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat ≤ M.cI →
        M.Solves ActSet.PIR {M.uPdot, M.uRPdot} M.uFPdot) ∧
      (M.γ0 / M.γ1 * (1 / M.D) * M.chat ≤ M.cI →
        M.cI < M.cR / (M.cP + M.β * M.γ1 * M.cF) * M.chat →
        M.Solves ActSet.PIR {M.uPdot, M.uRPdot, M.uIRP} M.uFPdot) ∧
      (M.cI < M.γ0 / M.γ1 * (1 / M.D) * M.chat → M.PIRStructure)) ∧
    -- (3) [PR], I[PR], [PIR]
    (M.cR < min (M.γ0 / M.γ1 * M.thrP) M.thrP →
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
            M.f m1 = (M.withCI c1).g m2) := by sorry

end MaintPOMDP.Frontier
