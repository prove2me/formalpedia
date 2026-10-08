-- Prove2me | Theorems.Thm_KumarSeidman_CAF_gamma_implication
-- name    : KumarSeidman.CAF.gamma_implication
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:00.185986+00:00
-- url     : https://prove2.me/theorems/e947d3ec-4f34-41e0-9857-007a86a087bf
-- title:
--   Proof of Theorem 1: V_m(T_n) ≥ Γ_m implies V_m(T_{n+1}) ≤ V_m(T_n) − δ̄ on minimal classes
-- statement:
--   Let the system satisfy (14) and consider a trajectory under a CAF policy with constants $\varepsilon_{m'}>0$, $K_{m'}$. Let $m$ be a machine whose class is minimal, with $B_m\neq\emptyset$, and let $T_n,T_{n+1}$ be consecutive set-up commencements of $m$. With
--
--   $$
--   \Gamma_m=\max\Big(\frac{2\bar\delta\bar\tau}{\varepsilon_m\underline\tau(1-\rho'_m)}+\frac{K_m\bar\tau}{\varepsilon_m},\ \bar\delta\Big),
--   $$
--
--   where $\bar\tau$ is the largest remaining work at $m$ of a part in a buffer of $m$ and $\underline\tau$ the smallest processing time at $m$, one has
--
--   $$
--   V_m(T_n)\ \ge\ \Gamma_m\quad\Longrightarrow\quad V_m(T_{n+1})\ \le\ V_m(T_n)-\bar\delta .
--   $$
--
--   This is the step that yields ultimate boundedness of $V_m$ at set-up epochs: above the explicit level $\Gamma_m$, $V_m$ cannot increase from one set-up commencement to the next.
--
--   **Formalization Note** $T_n=s_k$, $T_{n+1}=s_{k+1}$ with $k\ge1$. All divisions are by positive quantities: $\varepsilon_m>0$ (CAF), $\underline\tau>0$, $1-\rho'_m>0$ (14). $K_m$ is any real. When $\bar\delta=0$ the conclusion reads $V_m(T_{n+1})\le V_m(T_n)$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 295, proof of Theorem 1, display after (22) with Γ_m

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- The `Γ_m` implication (p. 295, after (22)): under (14) and a CAF policy with constants
`ε, K`, for a machine `m` whose class is minimal and two consecutive set-up commencements
`T_n = s_k`, `T_{n+1} = s_{k+1}` (`k ≥ 1`) at `m`,
`V_m(T_n) ≥ Γ_m ⇒ V_m(T_{n+1}) ≤ V_m(T_n) − δ̄`, where
`Γ_m = max (2 δ̄ τ̄ / (ε_m τ̲ (1 − ρ'_m)) + K_m τ̄ / ε_m, δ̄)`. -/
theorem gamma_implication {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) (m : Fin M)
    (hmin : S.IsMinimal m) (hB : (S.B m).Nonempty) (k : ℕ) (hk : 1 ≤ k)
    (hnext : T.HasNext m k) (hV : S.Gamma m hB ε K ≤ T.V m (T.s m k)) :
    T.V m (T.s m (k + 1)) ≤ T.V m (T.s m k) - S.deltaBar m := by sorry

end KumarSeidman.CAF
