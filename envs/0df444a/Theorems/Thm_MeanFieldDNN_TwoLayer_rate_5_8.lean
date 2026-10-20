-- Prove2me | Theorems.Thm_MeanFieldDNN_TwoLayer_rate_5_8
-- name    : MeanFieldDNN.TwoLayer.rate_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:25:02.989507+00:00
-- url     : https://prove2.me/theorems/c856a896-b661-4527-9ba0-a997103627d9
-- title:
--   §5.8 — $N_2^{-1/2}$ output convergence rate
-- statement:
--   Fix a solution of (2.6). For the output $g_t^{N_2}$ of a solution of (5.1), there is a constant $K$ independent of $N_2$, the particle solution, $t\in[0,1]$, and $x\in X$ such that
--
--   $$\mathbb E[|g_t^{N_2}(x)-g_t(x)|]\le K/\sqrt{N_2}.$$
--
--   This is the quantitative second-width conclusion of Theorem 2.3. The expectation integrates the independent initial output-weight vector.
-- source:
--   Sirignano, Spiliopoulos, Mean Field Analysis of Deep Neural Networks, arXiv:1903.04440v5, p. 25, §5.8, displayed rate

import Mathlib
import Definitions.Def_MeanFieldDNN_TwoLayer_Model

open MeasureTheory Filter Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace MeanFieldDNN.TwoLayer

theorem rate_5_8 {d : ℕ} (S : Setting d) (L : LimitPaths d)
    (hL : IsLimitSolution S L) :
    ∃ K : ℝ, ∀ (N2 : ℕ), 1 ≤ N2 → ∀ Q : ParticlePaths d N2,
      IsParticleSolution S N2 Q → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ S.X,
        (∫ cv : Fin N2 → ℝ, |partG S Q t cv x - limG S L t x|
          ∂(Measure.pi fun _ : Fin N2 => S.μc)) ≤ K / Real.sqrt (N2 : ℝ) := by sorry
end MeanFieldDNN.TwoLayer
