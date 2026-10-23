-- Prove2me | Theorems.Thm_NonconvexCost_Complexity_eq_4_4
-- name    : NonconvexCost.Complexity.eq_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:45.400926+00:00
-- url     : https://prove2.me/theorems/145a5e3a-8d2c-437e-a12b-0cded766358f
-- title:
--   (4.4), p. 10 (corrected) — Algorithm 4.1 starts at most (⌊3(f(x₀) − inf f)/(δε)⌋ + 1)·16L²/ε² line searches
-- statement:
--   Let $\delta,\epsilon>0$, let $C\subset X$, let $f$ be bounded below on $C$, let $G$ be an $L$-bounded map $X\times X\to X$ ($L>0$, $|G(x,e)|\le L$), and let $x_0\in C$ satisfy
--   $$x\in C,\ f(x)\le f(x_0),\ |y|\le\delta\ \Longrightarrow\ x+y\in C .$$
--   Let $g_0\in\partial_\delta f(x_0)$ be a Goldstein subgradient. Then for every $n$, the number of line searches started during the first $n$ steps of the run of Algorithm 4.1 from $(x_0,g_0)$ is at most
--   $$\Big(\Big\lfloor\frac{3(f(x_0)-\inf_C f)}{\delta\epsilon}\Big\rfloor+1\Big)\cdot\frac{16L^2}{\epsilon^2}.$$
--   A line search starts at a step where the run is at the subgradient test with $|g|>\epsilon$ and the trial point fails the sufficient-decrease test.
--
--   This bounds the number of line searches by the number of phases between reductions times the number of shortening steps per phase.
--
--   **Formalization Note** *Corrected.* The paper prints $\lceil 3(f(x_0)-\min f)/(\delta\epsilon)\rceil\cdot16L^2/\epsilon^2$, which is $0$ when $f(x_0)=\min f$; but a run started with $|g_0|>\epsilon$ at a minimiser where the trial step fails starts a line search at once. The proof on p. 10 gives at most $\lfloor3(f(x_0)-\inf f)/(\delta\epsilon)\rfloor$ reductions, hence that many plus one phases; the statement uses this count. "$\min f$" is the infimum over $C$.
-- source:
--   Kong, Lewis, The cost of nonconvexity in deterministic nonsmooth optimization, arXiv:2210.00652v2, p. 10, (4.4) (corrected phase count)

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm

namespace NonconvexCost.Complexity

open Classical in
theorem eq_4_4 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ ε L : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (C : Set X) (f : X → ℝ) (hbdd : BddBelow (f '' C))
    (G : X → X → X) (hL : IsLBounded G L) (x0 : X) (hx0 : x0 ∈ C)
    (hsub : ∀ x ∈ C, f x ≤ f x0 → ∀ y : X, ‖y‖ ≤ δ → x + y ∈ C)
    (g0 : X) (hg0 : g0 ∈ goldstein G δ x0) (n : ℕ) :
    (((Finset.range n).filter (fun j => StartsLineSearch f δ ε (run f G δ ε x0 g0 j))).card : ℝ) ≤
      ((⌊3 * (f x0 - sInf (f '' C)) / (δ * ε)⌋₊ : ℝ) + 1) * (16 * L ^ 2 / ε ^ 2) := by sorry

end NonconvexCost.Complexity
