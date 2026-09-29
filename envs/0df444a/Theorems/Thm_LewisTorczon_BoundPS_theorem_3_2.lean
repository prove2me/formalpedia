-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_theorem_3_2
-- name    : LewisTorczon.BoundPS.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:48:32.844455+00:00
-- url     : https://prove2.me/theorems/7ba778f2-c598-48a0-8e95-5dd240671920
-- title:
--   Theorem 3.2 — $\liminf_{k\to\infty}\|q(x_k)\|=0$
-- statement:
--   Let $x_k$ be the iterates of a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):\ell\le x\le u\}$ (Algorithm 1). Suppose that $L_\Omega(x_0)=\{x\in\Omega:f(x)\le f(x_0)\}$ is compact and that $f$ is continuously differentiable on an open set containing $\Omega$. Then, with $q(x)=P(x-\nabla f(x))-x$,
--   $$\liminf_{k\to\infty}\|q(x_k)\|=0 .$$
--
--   This is the first global convergence result for the method: some subsequence of the iterates approaches first-order stationarity for the bound constrained problem, with no derivative ever computed by the algorithm.
--
--   **Formalization Note** Since $\|q(x_k)\|\ge0$, "$\liminf=0$" is encoded as: for every $\varepsilon>0$, $\|q(x_k)\|<\varepsilon$ for infinitely many $k$. The page assumes $f$ continuously differentiable on $L_\Omega(x_0)$; the statement assumes it on an open set $U\supseteq\Omega$, because the proof evaluates $\nabla f$ at trial points in $\Omega$ outside $L_\Omega(x_0)$, and because $L_\Omega(x_0)$ may have empty interior.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 7, Theorem 3.2 (proof in §4.1, p. 11)

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Theorem 3.2**, p. 7: if `L_Ω(x_0)` is compact and `f` is `C¹`, the iterates of a generalized
pattern search method for bound constrained minimization satisfy
`liminf_{k→∞} ‖q(x_k)‖ = 0`, encoded as `‖q(x_k)‖ < ε` infinitely often for every `ε > 0`. -/
theorem theorem_3_2 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) :
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ‖projQ lo hi f (R.x k)‖ < ε := by sorry

end LewisTorczon.BoundPS
