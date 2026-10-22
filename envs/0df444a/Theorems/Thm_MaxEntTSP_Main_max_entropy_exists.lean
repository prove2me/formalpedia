-- Prove2me | Theorems.Thm_MaxEntTSP_Main_max_entropy_exists
-- name    : MaxEntTSP.Main.max_entropy_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:19.491931+00:00
-- url     : https://prove2.me/theorems/56f6424a-ab83-43c9-a1fc-54bb3158868c
-- title:
--   §2.2, p. 6 — existence of an exact maximum-entropy spanning-tree law
-- statement:
--   On a rooted Held–Karp instance with $x^0_{e_0}=1$, there exists a probability law $\mu$ on spanning trees of the remaining support $E$ with marginal $x^0_e$ for every $e\in E$, and with maximal entropy among all such laws:
--   $$\exists\mu\;\forall\nu\text{ with the same tree support and marginals},\quad H(\nu)\le H(\mu).$$
--
--   This makes the maximum-entropy assumption in the main theorem satisfiable. The result follows from the spanning-tree polytope characterization and finite-dimensional entropy maximization; it does not assert that a finite-parameter $\lambda$-uniform law with exact marginals exists on the boundary.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, p. 2 (PDF 4), §1.1, maximum-entropy paragraph and footnote 2; p. 6 (PDF 8), Fact 2.1 and Edmonds paragraph

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Edmonds' spanning-tree polytope and finite entropy maximization. -/
theorem max_entropy_exists (m : ℕ) (hm : 3 ≤ m)
    (x : Fin m → Fin m → ℝ) (hx : IsHeldKarp x)
    (a b : Fin m) (hab : a ≠ b) (he0 : x a b = 1) :
    ∃ μ : Finset (Sym2 (Fin m)) → ℝ, IsMaxEntropy (lpSupport x a b) x μ := by sorry

end MaxEntTSP.Main
