-- Prove2me | Theorems.Thm_KumarSeidman_CAF_minimal_class_bounded
-- name    : KumarSeidman.CAF.minimal_class_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:05.471241+00:00
-- url     : https://prove2.me/theorems/e13b8c6c-3c06-4013-a46e-6a77dbc9ff5a
-- title:
--   Proof of Theorem 1: under CAF and (14), the buffers of machines in minimal classes are bounded
-- statement:
--   Let the system satisfy (14), and consider a trajectory under a CAF policy with constants $\varepsilon_{m'}>0$, $K_{m'}$, from any initial state. If the class of machine $m$ is minimal for the partial order on diconnected classes (no other class has a path into it), then every buffer of $m$ is bounded over all time:
--
--   $$
--   \sup_{0\le t<\infty}x_{p,i}(t)<+\infty\qquad\text{for every } (p,i)\text{ with } \mu_{p,i}=m .
--   $$
--
--   This is the base case of the induction over the classes of machines that proves Theorem 1.
--
--   **Formalization Note** The bound may depend on the trajectory. Minimality is stated as: every machine from which $m$ is reachable is reachable from $m$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 295, proof of Theorem 1, boundedness on the minimal elements G_1, …, G_l

import Mathlib
import Definitions.Def_KumarSeidman_CAF_System
import Definitions.Def_KumarSeidman_CAF_Trajectory
import Definitions.Def_KumarSeidman_CAF_Policy
import Definitions.Def_KumarSeidman_CAF_Lyapunov

namespace KumarSeidman.CAF

/-- Boundedness on the minimal classes (p. 295): under (14) and a CAF policy, the levels of
the buffers of every machine `m` whose class is minimal are bounded on `[0, ∞)`. -/
theorem minimal_class_bounded {P M : ℕ} (S : System P M) (h14 : S.StringentCapacityCondition)
    (ε K : Fin M → ℝ) (T : Trajectory S) (hT : T.IsCAF ε K) (m : Fin M)
    (hmin : S.IsMinimal m) :
    ∀ b ∈ S.B m, ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → T.x b t ≤ C := by sorry

end KumarSeidman.CAF
