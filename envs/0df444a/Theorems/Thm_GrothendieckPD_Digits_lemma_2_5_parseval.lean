-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_parseval
-- name    : GrothendieckPD.Digits.lemma_2_5_parseval
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:18.990134+00:00
-- url     : https://prove2.me/theorems/c5f9a8e4-810d-4a2d-a308-98c456b2b960
-- title:
--   Lemma 2.5: Hermite-energy Parseval identity for a sign function
-- statement:
--   For every measurable $f:\mathbb R^n\to\{\pm1\}$, the Hermite degree energies satisfy
--   $$\sum_{m=0}^{\infty}\langle\Pi_mf,\Pi_mf\rangle
--   =\sum_{m=0}^{\infty}\|\Pi_mf\|_2^2=\|f\|_2^2=1.$$
--   In particular, these nonnegative energies are summable. This is exactly the Parseval identity used at the end of the displayed Cauchy–Schwarz estimate in Lemma 2.5.
--
--   **Formalization Note** The energy $\langle\Pi_mf,\Pi_mf\rangle$ is encoded by `coeff m f f`, using the published finite Hermite-moment sum `GrothendieckLB.pmInner`.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.5 proof, p. 5: $\sum_k\|\Pi_k f\|_2^2=\|f\|_2^2=1$

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- The Parseval identity used in the proof of Lemma 2.5 (p. 5). -/
theorem lemma_2_5_parseval :
    ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ), GrothendieckLB.IsSignFn f →
      Summable (fun m => coeff m f f) ∧ ∑' m, coeff m f f = 1 := by sorry
