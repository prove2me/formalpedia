-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_recursive_work_recurrences
-- name    : NearlyOptimalPPR.Computation.recursive_work_recurrences
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:22.597568+00:00
-- url     : https://prove2.me/theorems/2c83602d-048e-4da5-ba4f-89b016ce83b5
-- title:
--   Per-level work recurrences for recursive PageRank
-- statement:
--   Fix an exact-solve primitive model. There are positive constants $C$ and a positive integer $c$ such that the uniform work envelopes of created recursive PageRank calls satisfy the following recurrences. Put
--
--   $$P=C\bigl(2+\log(2/\varepsilon)+\ell\bigr)^c.$$
--
--   For a call scale $N\ge1$ and block size $b$ specified by its schedule,
--
--   $$R_j(N)\le P\left(\frac{N^2}{b}+\frac NbR_{j+1}(b)\right)+PN\quad(j<\ell),$$
--
--   and at a leaf,
--
--   $$R_\ell(N)\le P\left(\frac{N^2}{b}+Nb\right).$$
--
--   Here $R_j(N)$ is the supremum of the charged work of actual created calls at level $j$ and scale $N$, including descendants and completed budget-crossing updates. Its definition assigns infinite work to an unclosed call. The constants depend only on the fixed primitive model and work uniformly for $0<\varepsilon\le1$, all depths, and all block schedules. These are the quantitative recurrences of Lemma 4.4.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, Lemma 4.4 p.18 and its finite-prefix counts, termination argument, and work accounting pp.28–29.

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal

theorem NearlyOptimalPPR.Computation.recursive_work_recurrences (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧ ∀ (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule),
      0 < ε → ε ≤ 1 →
      let P := overhead C c ε ℓ
      (∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N → let b := blockScale schedule ℓ j N
        workEnvelope m ε ℓ schedule j N ≤ ENNReal.ofReal P*
          (ENNReal.ofReal (N^2/b)+ENNReal.ofReal (N/b)*workEnvelope m ε ℓ schedule (j+1) b)+ENNReal.ofReal (P*N)) ∧
      (∀ N : ℝ, 1 ≤ N → let b := blockScale schedule ℓ ℓ N
        workEnvelope m ε ℓ schedule ℓ N ≤ ENNReal.ofReal (P*(N^2/b+N*b))) := by sorry
