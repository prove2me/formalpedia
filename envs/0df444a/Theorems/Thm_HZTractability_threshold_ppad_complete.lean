-- Prove2me | Theorems.Thm_HZTractability_threshold_ppad_complete
-- name    : HZTractability.threshold_ppad_complete
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:11:58.862747+00:00
-- url     : https://prove2.me/theorems/5b57e52b-9057-444c-923a-8255a619c0ae
-- title:
--   [DFHM24, Thm 4.23] (cited, p.6): threshold games with degrees at most two are PPAD-complete
-- statement:
--   Cited by the paper from Deligkas, Fearnley, Hollender and Melissourgos [DFHM24, Theorem 4.23]: for every fixed $\kappa$ with $0<\kappa<1/6$, finding a $\kappa$-threshold solution (Definition 2.1) of a nonempty directed graph in which every vertex has indegree at most two and outdegree at most two is PPAD-complete. That is, the problem is in PPAD and every problem in PPAD reduces to it by a polynomial-time search reduction.
--
--   This is the source problem of the reduction proving Theorem 1.1, used at $\kappa=1/200$.
--
--   **Formalization Note** Not proved in this paper. The search problem is `ThresholdDeg2 κ`.
--
--   Differences from the source:
--   - encoding: “PPAD-complete” (not defined in the paper) → the public `QuasiStrictNE.PPADComplete`: in PPAD (total and Levin-reducible to End-of-Line) and every PPAD problem reduces to it; reason: standard definition; it adds nothing the paper denies
--   - encoding: finding a threshold solution of a directed graph → a search problem on binary strings: instances are $0/1$ adjacency matrices of graphs on $n\ge1$ vertices with degrees at most two, answers rational $\kappa$-threshold solutions; reason: the paper fixes no encoding; graphs are nonempty as in §5.1, p.20; the solution set is a finite union of convex sets cut out by rational strict and non-strict inequalities, so a solution has a rational point
--   - reading: every fixed $0<\kappa<1/6$ → every rational $\kappa\in(0,1/6)$; reason: a fixed constant of a search problem over binary strings with rational answers is rational; for irrational $\kappa$ a rational answer need not exist; the paper uses $\kappa=1/200$
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §2.1, p.6 (PDF p.8), citing [DFHM24, Theorem 4.23]

import Mathlib
import Definitions.Def_QuasiStrictNE_PPADComplete
import Definitions.Def_HZTractability_ThresholdDeg2

namespace HZTractability

/-- **[DFHM24, Theorem 4.23], as quoted in** Panageas–Shein–Taherijam–Vazirani, *Exploring the
Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256
74b7bf9f…, §2.1, p.6 (PDF 8): "Such a solution always exists. Finding one is PPAD-complete for every
fixed 0 < κ < 1/6, even when both degrees are at most two [DFHM24, Theorem 4.23]."

For every rational `κ ∈ (0, 1/6)`, the search problem of finding a κ-threshold solution of a
nonempty directed graph with all in- and outdegrees at most two (`ThresholdDeg2 κ`) is
PPAD-complete: it is in PPAD (total and reducible to End-of-Line) and every PPAD problem reduces to
it.

**Formalization Note** Cited from [DFHM24]; not proved in this paper. PPAD-completeness is the public
`QuasiStrictNE.PPADComplete`. The fixed constant `κ` is rational, as a parameter of a search problem
over binary strings with rational answers must be (the paper uses `κ = 1/200`). -/
theorem threshold_ppad_complete (κ : ℚ) (hκ0 : 0 < κ) (hκ1 : κ < 1 / 6) :
    QuasiStrictNE.PPADComplete (ThresholdDeg2 κ) := by sorry

end HZTractability
