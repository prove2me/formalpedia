-- Prove2me | Theorems.Thm_KumarSeidman_CAF_drift_at_setups
-- name    : KumarSeidman.CAF.drift_at_setups
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:13.16201+00:00
-- url     : https://prove2.me/theorems/ce1ed975-22b6-470d-b989-0ce668664edf
-- title:
--   (18): drift of V_m between consecutive set-up commencements at a machine of a minimal class
-- statement:
--   Let the system satisfy condition (14), $\rho'_{m'}<1$ for every machine $m'$, and consider a trajectory under a clearing policy. Let $m$ be a machine whose class is minimal for the partial order of diconnected classes, and let $T_n\le T_{n+1}$ be two consecutive times at which $m$ commences a set-up. Then
--
--   $$
--   V_m(T_{n+1})\ \le\ \max\big[0,\ V_m(T_n)-(1-\rho'_m)(T_{n+1}-T_n)+\bar\delta\big],
--   $$
--
--   where $V_m$ is the Lyapunov function (15) and $\bar\delta$ the largest set-up time between buffers of $m$.
--
--   Over one cycle of machine $m$ the work it receives is at most $\rho'_m$ per unit time, while it completes work at unit rate except during the set-up and while starved; this drift inequality drives the boundedness of $V_m$ on minimal classes.
--
--   **Formalization Note** $T_n,T_{n+1}$ are the starts $s_k,s_{k+1}$ of two consecutive runs $k\ge1$ and $k+1$ of $m$, which need not be strictly ordered. Only the clearing property is assumed (the paper is in the CAF context, but (18) uses only Definition 1). $\bar\delta\ge0$ is not assumed positive; the paper's "$\bar\delta>0$" is a remark. The minimality of the class of $m$ is stated without quotients: every machine from which $m$ is reachable is reachable from $m$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 295, proof of Theorem 1, (18)

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- (18) (p. 295): under (14) and a clearing policy, for a machine `m` whose class is minimal
and two consecutive set-up commencements `T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_{n+1}) ≤ max [0, V_m(T_n) − (1 − ρ'_m)(T_{n+1} − T_n) + δ̄]`. -/
theorem drift_at_setups {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (T : Trajectory S) (hT : T.IsClearing) (m : Fin M) (hmin : S.IsMinimal m) (k : ℕ)
    (hk : 1 ≤ k) (hnext : T.HasNext m k) :
    T.V m (T.s m (k + 1)) ≤
      max 0 (T.V m (T.s m k) - (1 - S.rhoPrime m) * (T.s m (k + 1) - T.s m k)
        + S.deltaBar m) := by sorry

end KumarSeidman.CAF
