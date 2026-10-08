-- Prove2me | Theorems.Thm_NetworkControl_GeneralCosts_theorem_ecca_performance_v2
-- name    : NetworkControl.GeneralCosts.theorem_ecca_performance_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:10.070297+00:00
-- url     : https://prove2.me/theorems/98e7073c-e748-4fd6-a434-92e544374d6d
-- title:
--   Theorem 6.3 — ECCA performance bounds (corrected: nonnegative transmission rates)
-- statement:
--   Consider $L$ queues with backlogs $U_i(t)$, $U_i(0)=0$, an arbitrary topology-state process $S(t)$ and an arbitrary input process with $0\le A_i(t)\le\hat R$. Transmission rates are given by functions $C_i(P,S)\ge 0$ of the power vector $P$ and the channel state, satisfying the $\beta$-condition $C_i(P,S)\le C_i(P^{[i]},S)+\beta P_i$ for all admissible $P$ (where $P^{[i]}$ is $P$ with the $i$-th entry set to $0$). The Energy Constrained Control Algorithm (ECCA) runs, with parameters $V\ge 0$, $P_{\max}>0$ and $0<P_{av}<P_{\max}$:
--
--   * *flow control*: $R_i(t)=A_i(t)$ if $U_i(t)\le V$ and $R_i(t)=0$ otherwise;
--   * *power allocation*: $P(t)$ maximizes $\sum_i\big[U_i(t)\,C_i(P,S(t))-D(t)P_i\big]$ over $P\ge 0$ with $\sum_iP_i\le P_{\max}$;
--   * *virtual power queue* (6.13): $D(t+1)=\max[D(t)-P_{av},0]+\sum_iP_i(t)$, $D(0)=0$;
--   * *queue dynamics*: $U_i(t+1)=\max[U_i(t)-C_i(P(t),S(t)),0]+R_i(t)$.
--
--   Then for every sample path: (i) $U_i(t)\le V+\hat R$ for all $i,t$; (ii) $D(t)\le D_{\max}:=\beta V+\beta\hat R+P_{\max}$ for all $t$; (iii) the energy spent over any $T$-slot window satisfies $\sum_{\tau=t_0}^{t_0+T-1}\sum_iP_i(\tau)\le P_{av}T+D_{\max}$.
--
--   **Formalization Note.** The retired statement omitted the monograph's standing assumption that transmission rates are nonnegative; a negative "rate" made $\max[U-C,0]$ exceed $U$ and the backlog grew without bound even with no admissions (the accepted disproof). The corrected statement adds $C_i(P,S)\ge 0$ for all $P,S,i$. The $\beta$-condition is required, as in the monograph, only for admissible power vectors ($P\ge 0$, $\sum_iP_i\le P_{\max}$). This is a deterministic, sample-path statement: no probability space, expectation or i.i.d. assumption is involved; the throughput statement under i.i.d. arrivals and states (p. 117) is not part of this theorem.
-- source:
--   Georgiadis, Neely & Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Foundations and Trends in Networking 1(1), 2006, pp. 115-117, Theorem 6.3 (ECCA performance), with the virtual power queue (6.13), p. 114

import Mathlib
import Definitions.Def_NetworkControl_GeneralCosts_eccaAdmitted
import Definitions.Def_NetworkControl_GeneralCosts_virtualPowerQueue

namespace NetworkControl.GeneralCosts

/-- Theorem 6.3 (ECCA Performance), Georgiadis–Neely–Tassiulas pp. 115–117. For any topology
state process `S(t)` and any input process `A(t)` with `0 ≤ A_i(t) ≤ R̂`, the Energy Constrained
Control Algorithm — flow control `R_i(t) = eccaAdmitted (U_i(t)) V (A_i(t))`, power allocation
`P(t)` maximizing `Σ_i [U_i(t) C_i(P, S(t)) - D(t) P_i]` over `P ≥ 0`, `Σ_i P_i ≤ Pmax`, and the
virtual power queue `D(t)` of (6.13) — guarantees `U_i(t) ≤ V + R̂` for all `i, t`,
`D(t) ≤ βV + βR̂ + Pmax` for all `t`, and hence a total energy of at most `Pav·T + Dmax` over any
`T`-slot window. `hCbeta` is the `β`-condition `C_i(P,S) ≤ C_i(P^{[i]},S) + βP_i` of p. 117.

Corrected version: the transmission-rate functions are nonnegative, `C_i(P, S) ≥ 0`, as
everywhere in the monograph (the queueing law `max[U - C, 0] + R` presupposes it); the retired
version omitted this standing assumption, so a negative "rate" let the backlog grow without
bound. -/
theorem theorem_ecca_performance_v2
    {L : ℕ} {Chan : Type*}
    (V Rhat Pmax Pav β : ℝ) (hV : 0 ≤ V) (hRhat : 0 ≤ Rhat) (hPmax : 0 < Pmax)
    (hPav : 0 < Pav) (hPavLtPmax : Pav < Pmax) (hβ : 0 < β)
    (A : ℕ → Fin L → ℝ) (hA0 : ∀ t i, 0 ≤ A t i) (hAle : ∀ t i, A t i ≤ Rhat)
    (S : ℕ → Chan)
    (C : (Fin L → ℝ) → Chan → Fin L → ℝ)
    (hCnonneg : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), 0 ≤ C P s i)
    (hCbeta : ∀ (P : Fin L → ℝ) (s : Chan) (i : Fin L), (∀ j, 0 ≤ P j) →
      (∑ j : Fin L, P j) ≤ Pmax → C P s i ≤ C (Function.update P i 0) s i + β * P i)
    (U : ℕ → Fin L → ℝ) (hU0 : ∀ i : Fin L, U 0 i = 0)
    (P : ℕ → Fin L → ℝ) (hPnonneg : ∀ t : ℕ, ∀ i : Fin L, 0 ≤ P t i)
    (hPbudget : ∀ t : ℕ, (∑ i : Fin L, P t i) ≤ Pmax)
    (D : ℕ → ℝ) (hDeq : ∀ t : ℕ, D t = virtualPowerQueue P Pav t)
    (hPopt : ∀ t : ℕ, ∀ P' : Fin L → ℝ, (∀ i : Fin L, 0 ≤ P' i) → (∑ i : Fin L, P' i) ≤ Pmax →
      (∑ i : Fin L, (U t i * C P' (S t) i - D t * P' i))
        ≤ ∑ i : Fin L, (U t i * C (P t) (S t) i - D t * (P t) i))
    (hUrec : ∀ t : ℕ, ∀ i : Fin L,
      U (t + 1) i = max (U t i - C (P t) (S t) i) 0 + eccaAdmitted (U t i) V (A t i)) :
    (∀ t : ℕ, ∀ i : Fin L, U t i ≤ V + Rhat) ∧
      (∀ t : ℕ, D t ≤ β * V + β * Rhat + Pmax) ∧
      (∀ t0 T : ℕ, (∑ τ ∈ Finset.range T, ∑ i : Fin L, P (t0 + τ) i)
        ≤ Pav * (T : ℝ) + (β * V + β * Rhat + Pmax)) := by sorry

end NetworkControl.GeneralCosts
