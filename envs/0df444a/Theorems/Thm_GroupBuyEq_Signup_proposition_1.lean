-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_proposition_1
-- name    : GroupBuyEq.Signup.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:30.798459+00:00
-- url     : https://prove2.me/theorems/9df36426-0360-4d61-a054-46a6dbe77f24
-- title:
--   Proposition 1, pp. 10–11 — for d > 0, 0 < δ < p₀/2 a unique dynamic consumer equilibrium exists; threshold rule, recursion (6), H_k = 1 − F(ū_{k,t})
-- statement:
--   Consider the two-threshold group-buying model of Ming and Tunca on the window $[0,T]$, with Poisson arrival rate $\lambda_g>0$, thresholds $0<M_1\le M_2$, deposit $d>0$, base price $p_0$ and discount $0<\delta<p_0/2$, deal prices $p_1=p_0-\delta$, $p_2=p_1-\delta\ge d$, and a reservation utility with an atomless probability law $\mu$ and c.d.f. $F$. The paper states:
--
--   > For any $\lambda_g(\mathbf w)$, $d>0$, and $0<\delta<p_0/2$, there exists a unique dynamic consumer equilibrium. In equilibrium, a customer with utility $u$ arriving at time $t$ with $N_t=k$ signs up if and only if $u\ge\bar u_{k,t}$, where $\bar u_{k,t}$ is as defined in (3). The equilibrium is characterized by the solution to the dynamic recursive equation system
--   > $$\pi^i_k(t)=\lambda_g(\mathbf w)\int_t^T e^{-\lambda_g(\mathbf w)\int_t^s H_{k+1}(v)dv}H_{k+1}(s)\pi^i_{k+1}(s)ds,\quad\text{for } 0\le k<M_i,\ i=1,2,\qquad(6)$$
--   > with boundary conditions $\pi^1_k(t)=0$, $\pi^2_k(t)=1$, for $k\ge M_2$, $\pi^1_k(t)=1-\pi^2_k(t)$ for $M_1\le k<M_2$, and where $H_k(t)=1-F(\bar u_{k,t})$, for $k\ge0$. (7)
--
--   Precisely, the theorem asserts:
--   1. **Existence.** There is a dynamic consumer equilibrium $(\pi^1_k,\pi^2_k)_{k\ge0}$.
--   2. **Uniqueness.** Any two equilibria agree on $[0,T]$: $\pi^i_k(t)$ is the same for all $k\ge0$, $i=1,2$, $t\in[0,T]$ (hence so is $H_k$).
--   3. **Characterization.** In every equilibrium, for every $k\ge0$ and $t\in[0,T]$, writing $\bar u_{k,t}=\bar u(\pi^1_{k+1}(t),\pi^2_{k+1}(t))$:
--      - $V_k(u,t)\ge0$ if and only if $u\ge\bar u_{k,t}$, for every $u$;
--      - $H_k(t)=1-F(\bar u_{k,t})$, which is (7);
--      - for $0\le k<M_i$, $i=1,2$,
--   $$\pi^i_k(t)=\lambda_g\int_t^T e^{-\lambda_g\int_t^s H_k(v)\,dv}H_k(s)\,\pi^i_{k+1}(s)\,ds .$$
--
--   The proposition reduces the equilibrium of a continuous-time sign-up game with two deal thresholds to an explicit backward recursion over the number of sign-ups, which is the basis of the paper's structural estimation.
--
--   **Formalization Note** The recursion (6) is printed with $H_{k+1}$; it is stated with $H_k$. The next arrival after $N_t=k$ sees $k$ sign-ups and joins with probability $H_k$ (equations (4)–(5)), the derivation in the proof ends with $H_k$ in (A.14), and with $H_{k+1}$ the function $\pi_k$ would depend on $\pi_{k+2}$. The equilibrium is the solution of the conditioning equations (2), (4), (5) with the boundary conditions (see the definitions file), and (6), (7) are conclusions, not definitions. Uniqueness is on $[0,T]$, since beliefs are unconstrained outside the event window. $T>0$ and $\lambda_g>0$ are implicit on the page; the standing $d\le p_2$ is from p. 7. The paper's "$F$ has a density" is weakened to "$\mu$ has no atoms".
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), pp. 10–11 (PDF 11–12), Proposition 1, (6)–(7)

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem proposition_1 (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ] :
    (∃ E : Profile, IsEquilibrium P μ E) ∧
    (∀ E E' : Profile, IsEquilibrium P μ E → IsEquilibrium P μ E' → ∀ k : ℕ,
        Set.EqOn (E.pi1 k) (E'.pi1 k) (Set.Icc 0 P.T) ∧
          Set.EqOn (E.pi2 k) (E'.pi2 k) (Set.Icc 0 P.T)) ∧
    (∀ E : Profile, IsEquilibrium P μ E → ∀ k : ℕ, ∀ t ∈ Set.Icc 0 P.T,
        (∀ u : ℝ, 0 ≤ V P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) u ↔
            ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t) ≤ u) ∧
        H P μ E k t = 1 - ProbabilityTheory.cdf μ (ubar P (E.pi1 (k + 1) t) (E.pi2 (k + 1) t)) ∧
        (k < P.M2 → E.pi2 k t = P.lam * ∫ s in t..P.T,
            Real.exp (-(P.lam * ∫ v in t..s, H P μ E k v)) * H P μ E k s * E.pi2 (k + 1) s) ∧
        (k < P.M1 → E.pi1 k t = P.lam * ∫ s in t..P.T,
            Real.exp (-(P.lam * ∫ v in t..s, H P μ E k v)) * H P μ E k s * E.pi1 (k + 1) s)) := by sorry

end GroupBuyEq.Signup
