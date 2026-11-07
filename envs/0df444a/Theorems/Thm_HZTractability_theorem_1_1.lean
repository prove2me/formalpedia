-- Prove2me | Theorems.Thm_HZTractability_theorem_1_1
-- name    : HZTractability.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:36.162305+00:00
-- url     : https://prove2.me/theorems/8b4dcb5b-2f3d-46c7-90e9-d377daee6b16
-- title:
--   Theorem 1.1 — normalized additive $\varepsilon^*(a)/N$-equilibria with utilities in $\{0,a,1\}$ are PPAD-complete
-- statement:
--   For every fixed rational $a\in(0,1)$ there is a positive rational constant $\varepsilon^*(a)$ such that computing a normalized additive $\varepsilon^*(a)/N$-equilibrium (Definition 2.2) of an $N$-buyer HZ market is PPAD-complete when all utilities belong to $\{0,a,1\}$.
--
--   Precisely: the search problem whose instances are the $N\times N$ utility matrices with $N\ge1$ and entries in $\{0,a,1\}$, and whose answers are normalized additive $\varepsilon^*(a)/N$-equilibria, is in PPAD and every problem in PPAD reduces to it by a polynomial-time search reduction.
--
--   This settles the complexity of HZ markets between the tractable bi-valued case and the four-valued hardness of [CCPY22]; since $1/\varepsilon=N/\varepsilon^*(a)$ is polynomial, it rules out an FPTAS unless PPAD $\subseteq$ P.
--
--   Differences from the source:
--   - encoding: “PPAD-complete” (not defined in the paper) → the public `QuasiStrictNE.PPADComplete`: in PPAD (total and Levin-reducible to End-of-Line) and every PPAD problem reduces to it; reason: standard definition; it adds nothing the paper denies
--   - encoding: “computing … of an $N$-buyer HZ market” → the search problem `HZThreeValue a ε*` on binary strings: instances `encRatMatrix N u` with $N\ge1$, $u_{ij}\in\{0,a,1\}$; answers codes of rational $(x,p)$ forming a normalized additive $(\varepsilon^*/N)$-equilibrium; reason: the paper fixes no encoding; Lemma 4.11 makes rational answers of polynomial length available
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_QuasiStrictNE_PPADComplete
import Definitions.Def_HZTractability_HZThreeValue

namespace HZTractability

/-- **Theorem 1.1** (Panageas–Shein–Taherijam–Vazirani, *Exploring the Tractability Frontier of
Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256 74b7bf9f…, p.1 (PDF 3)): "For
every fixed rational a ∈ (0, 1), there is a positive rational constant ε∗(a) such that computing a
normalized additive ε∗(a)/N-equilibrium of an N-buyer HZ market is PPAD-complete when all
utilities belong to {0, a, 1}."

For every rational `a ∈ (0, 1)` there is a rational `ε* > 0` such that the search problem
`HZThreeValue a ε*` — given `N ≥ 1` and an `N × N` utility matrix with entries in `{0, a, 1}`, find
a rational normalized additive `(ε*/N)`-equilibrium (Definition 2.2) — is PPAD-complete: it is in
PPAD (total and reducible to End-of-Line) and every PPAD problem reduces to it.

**Formalization Note** PPAD-completeness is the public `QuasiStrictNE.PPADComplete` (Levin search
reductions on Cook machines). `ε*` depends only on `a`; the accuracy `ε*/N` uses the instance's
`N`. Instances and answers are binary codes of rational matrices and vectors. -/
theorem theorem_1_1 (a : ℚ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ ε : ℚ, 0 < ε ∧ QuasiStrictNE.PPADComplete (HZThreeValue a ε) := by sorry

end HZTractability
