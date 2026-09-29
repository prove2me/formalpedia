-- Prove2me | Theorems.Thm_GKP1998_mass_radius_relation
-- name    : GKP1998.mass_radius_relation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:53:46.754452+00:00
-- url     : https://prove2.me/theorems/ae54ea23-b89e-4d50-a738-e26f1fae3923
-- title:
--   Eq. (41): $(mR)^2=4n\,g_{YM}\sqrt{2N}$ for a level-$n$ string state
-- statement:
--   Let $n\in\mathbb N$ and $N,g_{YM},\alpha',m,R>0$ with $m^2=4n/\alpha'$ and $R^4=2Ng_{YM}^2\alpha'^2$. Then $(mR)^2=4n\,g_{YM}\sqrt{2N}$.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 112, Eq. (41) and following text

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eq. (41), second part: with `m² = 4n/α'` (level-`n` string state) and
`R⁴ = 2 N g_YM² α'²`, one has `(mR)² = 4 n g_YM √(2N)`. -/
theorem mass_radius_relation (n : ℕ) (N gYM α' m R : ℝ) (hN : 0 < N) (hg : 0 < gYM)
    (hα : 0 < α') (hm : 0 < m) (hR : 0 < R) (hmass : m ^ 2 = 4 * n / α')
    (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2) :
    (m * R) ^ 2 = 4 * n * gYM * Real.sqrt (2 * N) := by sorry
end GKP1998
