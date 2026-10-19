-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_hierarchyStieltjesRatio_append_of_escaping
-- name    : MetricCodes.Spherical.HigherHierarchy.tendsto_hierarchyStieltjesRatio_append_of_escaping
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/683043ea-b54e-426a-b4ef-76c8e1aea0b3
-- title:
--   MetricCodes.Spherical.HigherHierarchy.tendsto_hierarchyStieltjesRatio_append_of_escaping
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.tendsto_hierarchyStieltjesRatio_append_of_escaping
    {k r : ℕ}
    {u v : ℕ → Fin k → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ}
    {d : Fin k → ℝ}
    (hu : ∀ i, Tendsto (fun n => u n i) atTop atTop)
    (hd : ∀ i, Tendsto (fun n => v n i / u n i) atTop (𝓝 (d i)))
    (ha : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (A i)))
    (hb : ∀ i, Tendsto (fun n => b n i) atTop (𝓝 (B i)))
    (hA : ∀ i, 0 ≤ A i)
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun n => hierarchyStieltjesRatio
        (Fin.append (m := k) (n := r + 1) (u n) (a n))
        (Fin.append (m := k) (n := r) (v n) (b n)) t)
      atTop
      (𝓝 ((∏ i : Fin k, d i ^ 2) * hierarchyStieltjesRatio A B t)) := by sorry
