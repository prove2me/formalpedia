-- Prove2me | Theorems.Thm_ImpulseGames_CostMonotonicity_xstar_monotone
-- name    : ImpulseGames.CostMonotonicity.xstar_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:40:21.313513+00:00
-- url     : https://prove2.me/theorems/0a4c1927-2417-4d2d-b43a-80d87205dad6
-- title:
--   Proposition 4.14 (corrected) — for $\tilde c=0$, $x_2^*$ decreases and $x_1^*$ increases in $c$; $x_2^*<\tilde s<x_1^*$ when also $\lambda=\tilde\lambda$
-- statement:
--   Under the standing assumptions of Section 4.1, assume moreover that the fixed gain vanishes, $\tilde c=0$. Let $x_1^*(c)$, $x_2^*(c)$ be the target states (4.20) of the linear impulse game with fixed intervention cost $c>0$. Then:
--
--   1. $c\mapsto x_2^*(c)$ is strictly decreasing on $]0,+\infty[$;
--   2. $c\mapsto x_1^*(c)$ is strictly increasing on $]0,+\infty[$;
--   3. if in addition $\lambda=\tilde\lambda$, then for every $c>0$
--   $$x_2^*(c) < \tilde s < x_1^*(c).$$
--
--   As the fixed cost grows, the state to which each player pushes the process moves away from the symmetry point $\tilde s$.
--
--   **Formalization Note.** The paper states the inequality $x_2^*<\tilde s<x_1^*$ under $\tilde c=0$ alone. Its proof uses $x_1^*(0^+)=x_2^*(0^+)=\tilde s$, which is Proposition 4.10 and requires $\lambda=\tilde\lambda$; for $\lambda>\tilde\lambda$ Proposition 4.11 gives $x_2^*(0^+)=\tilde s+\zeta>\tilde s$, and the inequality fails for small $c$ (e.g. $\rho=0.1$, $\sigma=0.3$, $\lambda=2$, $\tilde\lambda=1$, $\tilde s=0$, $c=0.01$ gives $x_2^*\approx0.076>0$). The hypothesis $\lambda=\tilde\lambda$ is therefore added to the inequality only. "Increasing" and "decreasing" are read strictly.
-- source:
--   Aïd et al. (2020), Math. Oper. Res. 45(1), accepted manuscript, Proposition 4.14 (pp. 22-23)

import Mathlib
import Definitions.Def_ImpulseGames_CostMonotonicity_Thresholds

namespace ImpulseGames.CostMonotonicity

theorem xstar_monotone (P : Params) (hP : P.Standing) (hct : P.cTilde = 0) :
    StrictAntiOn P.xstar2 (Set.Ioi 0) ∧ StrictMonoOn P.xstar1 (Set.Ioi 0) ∧
      (P.lam = P.lamTilde →
        ∀ c : ℝ, 0 < c → P.xstar2 c < P.sTilde ∧ P.sTilde < P.xstar1 c) := by sorry

end ImpulseGames.CostMonotonicity
