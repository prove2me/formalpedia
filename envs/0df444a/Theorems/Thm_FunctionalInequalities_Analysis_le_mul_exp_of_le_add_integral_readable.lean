-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_le_mul_exp_of_le_add_integral_readable
-- name    : FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:56.359354+00:00
-- url     : https://prove2.me/theorems/a6bad570-f51c-4919-9c6a-567bf7f49ada
-- title:
--   Integral Grönwall Bound
-- statement:
--   This statement is an integral Grönwall inequality.
--
--   Let φ:ℝ→ℝ and a,K,T∈ℝ. Assume K≥0, φ is measurable, φ is bounded on $[0,T]$, and for every t∈[0,T],
--
--   $$φ(t)\leq a+K\int_{(0,t]}φ(s)\,ds.$$
--
--   Then for every t∈[0,T],
--
--   $$φ(t)\leq a e^{Kt}.$$
--
--   This provides a real-analysis form of Grönwall's inequality for a measurable bounded function and an arbitrary real initial coefficient a.
--
--   **Formalization Note** The integral is over `Set.Ioc 0 t`; the theorem does not assume T≥0 separately, although the interval hypotheses govern its scope.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem le_mul_exp_of_le_add_integral {φ : ℝ → ℝ} {a K T : ℝ} (hK : 0 ≤ K)
--       (hφm : Measurable φ) (hφb : ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, |φ t| ≤ B)
--       (h : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a + K * ∫ s in Set.Ioc (0 : ℝ) t, φ s) :
--       ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a * Real.exp (K * t)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Gronwall`](https://prove2.me/theorems/cd710807-c023-4a0e-9183-faaa7308f99a).
--
--   [Source excerpt, lines 19–22](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Gronwall.lean#L19-L22) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Gronwall.lean#L18-L81 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Gronwall`, declaration `FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Gronwall

theorem FunctionalInequalities.Analysis.le_mul_exp_of_le_add_integral_readable {φ : ℝ → ℝ} {a K T : ℝ} (hK : 0 ≤ K)
    (hφm : Measurable φ) (hφb : ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, |φ t| ≤ B)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a + K * ∫ s in Set.Ioc (0 : ℝ) t, φ s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ a * Real.exp (K * t) := by sorry
