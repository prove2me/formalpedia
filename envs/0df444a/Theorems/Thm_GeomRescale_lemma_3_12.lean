-- Prove2me | Theorems.Thm_GeomRescale_lemma_3_12
-- name    : GeomRescale.lemma_3_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:29.654599+00:00
-- url     : https://prove2.me/theorems/4b85dac2-3bed-49a0-bc83-97e1d0d823a0
-- title:
--   Lemma 3.12: $\det R$ grows by $16/9$ at every rescaling
-- statement:
--   The determinant of $R$ increases at least by a factor $16/9$ at every rescaling of Algorithm Rescaling-SFM:
--
--   $$\det R' \ge \frac{16}{9} \det R.$$
--
--   This uses $\varepsilon = 1/(20n)$.
--
--   Differences from the source:
--   - encoding: every rescaling → every step between reachable states that increments the rescaling count; reason: only the rescaling step does
--   - encoding: a ground set $V$ with $n = |V|$ elements → `1 ≤ n`; reason: the parameter $\varepsilon = 1/(20n)$ of Algorithm 2 is undefined at $n = 0$; the hypothesis excludes only that case
--   - generalization: the run of Algorithm 2 with $T = 5n\log(nL_{f,2})$ → the runs for every $\Lambda \ge L_{f,2}$, with $T = \lceil 5n\log_2(n\Lambda)\rceil_+$; reason: $\Lambda = L_{f,2}$ gives the paper's run, with $T$ rounded as in Theorem 3.6; the statement holds on every such run
--   - reading: $g/\|g\|_Q$ with no case for $g = 0$ → $g/\|g\|_Q := 0$ at $g = 0$ in the step relation; reason: $g = 0$ occurs (for $f \equiv 0$ at line 2 of Algorithm 1), and the run needs a value there
--   - reading: $g_1, \dots, g_k$ in (10) and in line 8 of Algorithm 2, returned after line 15 of Algorithm 1 incremented $k$ → $g_1, \dots, g_{k-1}$, the bases the call computed; reason: line 15 has incremented $k$, so no $g_k$ was computed
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.12, p.12, proof p.31

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_GeomRescale_fR
import Definitions.Def_GeomRescale_Ltwo
import Definitions.Def_GeomRescale_Reachable

open NonmonotoneSubmod.Shared
open SchrijverSFM.Alg

namespace GeomRescale

/-- Lemma 3.12 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Lemma 3.12, p.12, proof p.31): the determinant of `R` increases at least by a
factor `16/9` at every rescaling.

**Formalization Note.** A rescaling is a step between reachable states that increases the counter
`i`; `Step.rescale` is the only such step. -/
theorem lemma_3_12 {n : ℕ} (hn : 1 ≤ n) (f : Finset (Fin n) → ℤ) (hsub : Submodular (fR f))
    (hf0 : f ∅ = 0) (Λ : ℝ) (hΛ : Ltwo (fR f) ≤ Λ) (s s' : St n) (hs : Reachable f Λ s)
    (hstep : Step f Λ s s') (hi : s'.i = s.i + 1) :
    (16 / 9 : ℝ) * s.R.det ≤ s'.R.det := by sorry

end GeomRescale
