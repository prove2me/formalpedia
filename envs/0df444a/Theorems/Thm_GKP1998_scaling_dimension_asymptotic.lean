-- Prove2me | Theorems.Thm_GKP1998_scaling_dimension_asymptotic
-- name    : GKP1998.scaling_dimension_asymptotic
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:54:06.942266+00:00
-- url     : https://prove2.me/theorems/91641efd-5612-477e-a55f-2469d7b3d9f5
-- title:
--   Eqs. (45)–(46): $\Delta\sim2(n\,g_{YM}\sqrt{2N})^{1/2}$ at strong coupling
-- statement:
--   For every integer $n\ge1$ and $N>0$,
--   $$\frac{2+\sqrt{4+4n\,g\sqrt{2N}}}{2\sqrt{n\,g\sqrt{2N}}}\longrightarrow1\qquad(g\to+\infty).$$
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, pp. 112-113, Eqs. (45)-(46)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (45)–(46): for a level-`n` state (`n ≥ 1`) the dimension
`Δ = 2 + √(4 + 4 n g_YM √(2N))` grows like `2 (n g_YM √(2N))^{1/2}` as `g_YM → ∞`
(`N` fixed), i.e. their ratio tends to `1`. -/
theorem scaling_dimension_asymptotic (n : ℕ) (hn : 1 ≤ n) (N : ℝ) (hN : 0 < N) :
    Tendsto (fun gYM : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * gYM * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by sorry
end GKP1998
