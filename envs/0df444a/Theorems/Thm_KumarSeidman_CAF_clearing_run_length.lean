-- Prove2me | Theorems.Thm_KumarSeidman_CAF_clearing_run_length
-- name    : KumarSeidman.CAF.clearing_run_length
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:34.528967+00:00
-- url     : https://prove2.me/theorems/8095a6f9-dc79-4723-a20e-735d7b534bc3
-- title:
--   (20): a large buffer at a set-up commencement forces a long clearing run
-- statement:
--   Consider a trajectory under a clearing policy and a machine $m$ with $\rho'_m<1$. Suppose $m$ commences a set-up to buffer $b_{p^*_n,i^*_n}$ at time $T_n$, and its next set-up commencement is at $T_{n+1}$. Then
--
--   $$
--   x_{p^*_n,i^*_n}(T_n)\ \ge\ \frac{2\bar\delta}{(1-\rho'_m)\,\tau_{p^*_n,i^*_n}}\quad\Longrightarrow\quad T_{n+1}-T_n\ \ge\ \frac{2\bar\delta}{1-\rho'_m}.
--   $$
--
--   The machine may only leave $b_{p^*_n,i^*_n}$ once it is empty, and it cannot empty it faster than at rate $1/\tau_{p^*_n,i^*_n}$; so long set-up-to-set-up cycles follow from large selected buffers, which is what amortizes the set-up time in the Lyapunov argument.
--
--   **Formalization Note** $T_n=s_k$ and $T_{n+1}=s_{k+1}$ for a run $k\ge1$ of $m$ that is followed by run $k+1$. Only the clearing property and $\rho'_m<1$ for this machine are assumed.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 295, proof of Theorem 1, (20)

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- (20) (p. 295): under a clearing policy, if machine `m` with `ρ'_m < 1` commences a set-up
to buffer `b* = β m k` at `T_n = s_k` (`k ≥ 1`) and its next set-up commencement is
`T_{n+1} = s_{k+1}`, then
`x_{b*}(T_n) ≥ 2 δ̄ / ((1 − ρ'_m) τ_{b*}) ⇒ T_{n+1} − T_n ≥ 2 δ̄ / (1 − ρ'_m)`. -/
theorem clearing_run_length {P M : ℕ} (S : System P M) (T : Trajectory S)
    (hT : T.IsClearing) (m : Fin M) (hρ : S.rhoPrime m < 1) (k : ℕ) (hk : 1 ≤ k)
    (hnext : T.HasNext m k)
    (hx : 2 * S.deltaBar m / ((1 - S.rhoPrime m) * S.tau (T.β m k)) ≤ T.x (T.β m k) (T.s m k)) :
    2 * S.deltaBar m / (1 - S.rhoPrime m) ≤ T.s m (k + 1) - T.s m k := by sorry

end KumarSeidman.CAF
