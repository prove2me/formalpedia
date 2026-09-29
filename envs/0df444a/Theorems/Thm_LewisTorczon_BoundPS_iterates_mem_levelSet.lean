-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_iterates_mem_levelSet
-- name    : LewisTorczon.BoundPS.iterates_mem_levelSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:44:59.933683+00:00
-- url     : https://prove2.me/theorems/d4c94b05-5992-4a35-b5a5-58f47b3077dc
-- title:
--   The iterates stay in $L_\Omega(x_0)$ (§4, proof of Theorem 4.5)
-- statement:
--   Let $x_k$ be the iterates of a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$. Then every iterate lies in the feasible level set of the starting point:
--   $$x_k\in L_\Omega(x_0)=\{x\in\Omega : f(x)\le f(x_0)\}\qquad\text{for all }k .$$
--
--   This is the fact that makes compactness of $L_\Omega(x_0)$ useful: all the analysis of the method takes place in that one compact set.
--
--   **Formalization Note** This is an unnumbered claim of the paper, made in the second paragraph of the proof of Theorem 4.5. No hypothesis on $f$ is needed.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 10, §4, proof of Theorem 4.5, second paragraph

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- §4, p. 10, proof of Theorem 4.5, second paragraph: all the iterates of a generalized pattern
search run lie in `L_Ω(x_0) = {x ∈ Ω : f(x) ≤ f(x_0)}`. -/
theorem iterates_mem_levelSet {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∀ k, R.x k ∈ levelSet lo hi f (R.x 0) := by sorry

end LewisTorczon.BoundPS
