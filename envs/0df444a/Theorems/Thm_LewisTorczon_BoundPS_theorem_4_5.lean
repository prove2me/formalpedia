-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_theorem_4_5
-- name    : LewisTorczon.BoundPS.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:47:58.821741+00:00
-- url     : https://prove2.me/theorems/ccbe9876-fc40-464c-acde-84127a8162af
-- title:
--   Theorem 4.5 — if $L_\Omega(x_0)$ is compact then $\liminf_k\Delta_k=0$
-- statement:
--   Let $x_k,\Delta_k$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):x\in\Omega\}$, and assume that $L_\Omega(x_0)=\{x\in\Omega:f(x)\le f(x_0)\}$ is compact. Then
--   $$\liminf_{k\to\infty}\Delta_k=0 .$$
--
--   No smoothness of $f$ is required: the result follows from the lattice structure of the iterates, the simple decrease rule, and the update rule for $\Delta_k$. It is the step-length half of the global convergence argument.
--
--   **Formalization Note** Since every $\Delta_k$ is positive, "$\liminf\Delta_k=0$" is encoded as: for every $\varepsilon>0$, $\Delta_k<\varepsilon$ for infinitely many $k$.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 10, Theorem 4.5

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Theorem 4.5**, p. 10: if `L_Ω(x_0)` is compact then `liminf_{k→∞} Δ_k = 0`, encoded as
`Δ_k < ε` infinitely often for every `ε > 0` (each `Δ_k > 0`). No smoothness of `f` is assumed. -/
theorem theorem_4_5 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (hcpt : IsCompact (levelSet lo hi f (R.x 0))) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, R.Δ k < ε := by sorry

end LewisTorczon.BoundPS
