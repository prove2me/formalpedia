-- Prove2me | Theorems.Thm_KumarSeidman_CAF_induction_recurrence
-- name    : KumarSeidman.CAF.induction_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:13.820245+00:00
-- url     : https://prove2.me/theorems/8a98f41c-0e17-4222-bdbf-92463e75afad
-- title:
--   Proof of Theorem 1, induction step: V_m(T_{n+1}) ≤ max{Γ̄, V_m(T_n) − (1 − ρ′_m)(T_{n+1} − T_n) + δ̄ + Γ̄}
-- statement:
--   Let the system satisfy (14) and consider a trajectory under a clearing policy. Let $U$ be a set of machines closed upstream (a machine with an arc into $U$ lies in $U$) such that the total content of the buffers of the machines in $U$ never exceeds $\Gamma$:
--
--   $$
--   \sum_{(p,i):\,\mu_{p,i}\in U}x_{p,i}(t)\le\Gamma\qquad\text{for all } t\ge0 .
--   $$
--
--   Let $m\notin U$ be a machine whose class is minimal among the machines outside $U$, and let $T_n,T_{n+1}$ be consecutive set-up commencements of $m$. Then
--
--   $$
--   V_m(T_{n+1})\ \le\ \max\big\{\bar\Gamma,\ V_m(T_n)-(1-\rho'_m)(T_{n+1}-T_n)+\bar\delta+\bar\Gamma\big\},
--   \qquad \bar\Gamma=\sum_{(p,i):\,\mu_{p,i}=m,\ \mu_{p,i-1}\ne m}\Gamma\,\big[\tau_{p,i}+\dots+\tau_{p,i+\eta_{p,i}-1}\big].
--   $$
--
--   This generalizes (17)–(18) to the machines of the next layer of classes, once the upstream layers are known to be bounded, and carries the induction of the proof of Theorem 1.
--
--   **Formalization Note** Three readings. (i) The paper's $\Gamma$ is "a bound on the buffers of such machines"; the inflow bound (23) it is used in requires a bound on their **total** content, which is what is assumed (a bound on each buffer separately would give $(i-1)\Gamma$ in (23)). (ii) The printed bound has the set-up time $\delta_{b_{p^*_n,i^*_n}}$ with an index missing; the statement uses $\bar\delta$, which dominates the set-up time actually paid at $T_n$, as in (18). (iii) Only the outer (simplified) inequality of the printed chain is stated. The classes already shown bounded are represented by an upstream-closed set $U$. $T_n=s_k$, $T_{n+1}=s_{k+1}$ with $k\ge1$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 295, proof of Theorem 1, induction step, (23) and the display after it

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- The recurrence of the induction step of the proof of Theorem 1 (p. 295, generalizing
(17)). Let `U` be an upstream-closed set of machines whose buffers have total content at most
`Γ` at all times `t ≥ 0`, and let `m ∉ U` be a machine whose class is minimal among the
machines outside `U`. Under (14) and a clearing policy, for two consecutive set-up
commencements `T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_{n+1}) ≤ max {Γ̄, V_m(T_n) − (1 − ρ'_m)(T_{n+1} − T_n) + δ̄ + Γ̄}`,
with `Γ̄ = Σ_{(p,i): μ_{p,i} = m, μ_{p,i−1} ≠ m} Γ [τ_{p,i} + ⋯ + τ_{p,i+η_{p,i}−1}]`. -/
theorem induction_recurrence {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (U : Finset (Fin M)) (hU : S.UpstreamClosed U)
    (Γ : ℝ) (hΓ : ∀ t : ℝ, 0 ≤ t →
      ∑ b ∈ Finset.univ.filter (fun b : Buffer S => S.mach b ∈ U), T.x b t ≤ Γ)
    (m : Fin M) (hmU : m ∉ U) (hmin : ∀ m' : Fin M, m' ∉ U → S.Reach m' m → S.Reach m m')
    (k : ℕ) (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max (S.GammaBar m Γ) (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m + S.GammaBar m Γ) := by sorry

end KumarSeidman.CAF
