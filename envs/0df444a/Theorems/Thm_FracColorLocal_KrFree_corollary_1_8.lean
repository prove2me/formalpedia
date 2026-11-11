-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_corollary_1_8
-- name    : FracColorLocal.KrFree.corollary_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:13:27.855627+00:00
-- url     : https://prove2.me/theorems/0e1d388a-50dc-4cbe-96af-9ce4b4ba6ef4
-- title:
--   Corollary 1.8 — G admits a φ-coloring for φ(v) = c_r f(d_{G,s}(v))
-- statement:
--   Let $r\ge4$, let $G$ be a finite $K_r$-free graph and $s$ a positive real vertex weight. Then $G$ admits a $\varphi$-coloring for
--
--   $$\varphi(v)=c_r\,f\big(d_{G,s}(v)\big)\qquad(v\in V(G)),$$
--
--   where $c_r$ is the constant of Theorem 1.7: rational, in $(0,1]$, and at least $\kappa_1/r$ for an absolute $\kappa_1>0$. Taking $s\equiv1$ gives Theorem 1.5.
--
--   Differences from the source:
--   - reading: "$c_r$" (the constant of Theorem 1.7) → for one absolute $\kappa_1>0$ and every $r\ge4$, some rational $c_r\in(0,1]$ with $c_r\ge\kappa_1/r$; reason: these are the properties Theorem 1.7 states for $c_r$, in the same quantifier shape as the Theorem 1.7 item.
--   - encoding: "a $K_r$-free graph $G$" → a graph on a finite type `V : Type`; reason: every finite graph is isomorphic to one on such a type.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 4 (PDF 5), Corollary 1.8; deduced p. 16 (PDF 17)

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_Shearer
import Definitions.Def_FracColorLocal_KrFree_PhiColoring
import Definitions.Def_FracColorLocal_KrFree_Potential

namespace FracColorLocal.KrFree

/-- Corollary 1.8, with `c_r` the constant of Theorem 1.7 (rational, in `(0, 1]`, at least
`κ₁/r` for one absolute `κ₁ > 0`): every `K_r`-free `G` admits a `φ`-coloring for
`φ(v) := c_r f(d_{G,s}(v))`, for every positive vertex weight `s`. -/
theorem corollary_1_8 :
    ∃ κ₁ : ℝ, 0 < κ₁ ∧
      ∀ r : ℕ, 4 ≤ r →
        ∃ c : ℚ, 0 < c ∧ c ≤ 1 ∧ κ₁ / r ≤ (c : ℝ) ∧
          ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree r →
            ∀ s : V → ℝ, (∀ v, 0 < s v) →
              HasPhiColoring G (fun v => (c : ℝ) * shearerF (weightedDegree G s v)) := by sorry

end FracColorLocal.KrFree
