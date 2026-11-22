-- Prove2me | Theorems.Thm_MasulloRepair_halfline_smooth_test_approximation
-- name    : MasulloRepair.halfline_smooth_test_approximation
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T15:03:39.305817+00:00
-- url     : https://prove2.me/theorems/c583dc66-557e-4b05-8068-c2038191323e
-- title:
--   Smooth positive-axis tests approximate every compact-window L2 function
-- statement:
--   Fix any $a,s\in\mathbf R$. Let $\nu_n$ be the positive-axis measures
--   $$d\nu_n(t)=1_{(0,\infty)}(t)\max\{t^{2a},t^{2(a+n)}\}
--   (1+\log^2t)^{s/2}\,\frac{dt}{t}\qquad(n\ge0).$$
--   If $f\in L^2(\nu_n)$ for every $n$, then there is one sequence $g_k\in C_c^\infty(\mathbf R;\mathbf C)$, with compact support contained in $(0,\infty)$, for which
--   $$g_k\in\bigcap_{n\ge0}L^2(\nu_n),\qquad
--   \lim_{k\to\infty}\|f-g_k\|_{L^2(\nu_n)}=0
--   \quad\text{for every fixed }n.$$
--
--   This proves the smooth-test approximation required by the compact-window repair, for every real endpoint $a$ and every real logarithmic weight parameter $s$. The approximants stay away from both zero and infinity individually. The compact support may grow with $k$, and the conclusion makes no assertion about a supremum over all windows.
--
--   **Formalization Note.** The support condition uses the closed support, and each $g_k$ is smooth on the entire real line, including across zero.
-- source:
--   Auxiliary theorem for the compact-window repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3), printed pp. 412-413, and Proposition 9.2.2.4, p. 414. Frozen source: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . This develops Yi's proposed compact-window replacement (mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2), after the accepted completeness theorem fea3483f-d6b8-43ba-95b4-3acb3895e88f. It is an explicitly stated repair, not a claim that the original uniform supremum is finite.

import Definitions.Def_MasulloRepair_LogWindows
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open MeasureTheory Set Filter Topology MasulloRepair
open scoped ENNReal ContDiff

theorem MasulloRepair.halfline_smooth_test_approximation (a s : ℝ) (f : ℝ → ℂ)
    (hf : ∀ n : ℕ, MemLp f 2 (windowMeasure (halflineBaseMeasure a s) n)) :
    ∃ g : ℕ → ℝ → ℂ,
      (∀ k, HasCompactSupport (g k) ∧
        tsupport (g k) ⊆ Ioi (0 : ℝ) ∧ ContDiff ℝ ∞ (g k)) ∧
      (∀ n k, MemLp (g k) 2 (windowMeasure (halflineBaseMeasure a s) n)) ∧
      ∀ n, Tendsto (fun k => eLpNorm (f - g k) 2
        (windowMeasure (halflineBaseMeasure a s) n)) atTop (𝓝 0) := by sorry
