-- Prove2me | Theorems.Thm_FracColorLocal_KrFree_theorem_1_5
-- name    : FracColorLocal.KrFree.theorem_1_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:12:20.956343+00:00
-- url     : https://prove2.me/theorems/d4b6af3b-31a5-4c3e-8ac8-5f216bd37e2e
-- title:
--   Theorem 1.5 — every K_r-free graph admits a φ-coloring for demands φ(v) ≤ (κ/r)·log(d(v)+2)/(d(v)+1)
-- statement:
--   There is an absolute constant $\kappa>0$ such that the following holds for every integer $r\ge4$. Every finite $K_r$-free graph $G$ admits a $\varphi$-coloring for every demand function $\varphi:V(G)\to[0,1]$ satisfying
--
--   $$\varphi(v)\ \le\ \frac{\kappa}{r}\cdot\frac{\log(d_G(v)+2)}{d_G(v)+1}\qquad(v\in V(G)),$$
--
--   where $d_G(v)$ is the degree of $v$ and $\log$ is the natural logarithm. A $\varphi$-coloring is a probability distribution on the independent sets of $G$ under which every vertex $v$ lies in the sampled set with probability at least $\varphi(v)$. The constant $\kappa$ is chosen before $r$, $G$ and $\varphi$; every degree, including degree $0$, is allowed, and the empty graph is included.
--
--   This confirms the Kelly–Postle conjecture (Conjecture 1.4) with $a_r=\kappa/r$; taking expected sizes gives a degree-sequence strengthening of the Ajtai–Erdős–Komlós–Szemerédi conjecture.
--
--   Differences from the source:
--   - encoding: "a $K_r$-free graph $G$" → a graph on a finite type `V : Type` with a `DecidableRel G.Adj` instance (used by `G.degree`); reason: every finite graph is isomorphic to one on such a type, and all decidability instances agree.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 3 (PDF 4), Theorem 1.5; deduced p. 16 (PDF 17)

import Mathlib
import Definitions.Def_FracColorLocal_KrFree_PhiColoring

namespace FracColorLocal.KrFree

/-- Theorem 1.5 (Kelly–Postle conjecture, with `a_r = κ/r`). -/
theorem theorem_1_5 :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ r : ℕ, 4 ≤ r →
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
          G.CliqueFree r →
          ∀ φ : V → ℝ, IsDemandFunction φ →
            (∀ v, φ v ≤ κ / r * (Real.log ((G.degree v : ℝ) + 2) / ((G.degree v : ℝ) + 1))) →
            HasPhiColoring G φ := by sorry

end FracColorLocal.KrFree
