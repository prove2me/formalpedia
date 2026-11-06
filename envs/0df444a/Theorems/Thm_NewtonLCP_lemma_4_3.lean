-- Prove2me | Theorems.Thm_NewtonLCP_lemma_4_3
-- name    : NewtonLCP.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:38.542966+00:00
-- url     : https://prove2.me/theorems/00a89e83-a9b1-47ad-98d3-8560115cb45e
-- title:
--   Lemma 4.3 — the Newton step squares the centrality error
-- statement:
--   Let $M\in\mathcal P_\star$, $(x,s)\in\mathcal F_{>0}(M,q)$ and $\mu>0$; let $(\Delta x,\Delta s)$ be the Newton step (10) from $(x,s,\mu)$ and $(x',s')=(x+\Delta x,s+\Delta s)$. Then
--
--   $$\mathrm{err}(x',s',\mu)=\big(H_{x,\mu}\,\mathrm{err}(x,s,\mu)\big)^2,$$
--
--   where the square is entrywise. This identity drives every convergence bound of the mission: the new error is the square of the relative step $\Delta x/x$.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 4.3, p.13

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_NewtonStep

open Matrix

namespace NewtonLCP

/-- **Lemma 4.3** (reducing centrality error). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 4.3, p.13 (proof (11), p.13).

Let `M ∈ P⋆`, `(x, s) ∈ F_{>0}` and `µ > 0`, `(∆x, ∆s)` the solution to (10), and
`(x', s') = (x + ∆x, s + ∆s)`. Then `err(x', s', µ) = (H_{x,µ} err(x, s, µ))²` (entrywise
square). -/
theorem lemma_4_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q x s : ι → ℝ)
    (mu : ℝ) (hM : IsPStar M) (hxs : (x, s) ∈ FeasPos M q) (hmu : 0 < mu) :
    err (x + newtonDx M x s mu) (s + newtonDs M x s mu) mu =
      fun i => (newtonMatrix M x mu *ᵥ err x s mu) i ^ 2 := by sorry

end NewtonLCP
