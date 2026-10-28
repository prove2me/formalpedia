-- Prove2me | Theorems.Thm_OAI_KServer_JointBudget_quota_bound
-- name    : OAI.KServer.JointBudget.quota_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T15:01:38.563183+00:00
-- url     : https://prove2.me/theorems/72087f6f-d452-49fb-b4d2-1c3c0c7297a2
-- title:
--   OAI.KServer.JointBudget.quota_bound: intermediate lemma from OpenAI, Squared-logarithmic randomized k-server on arbitrary metrics
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KServer.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Squared-logarithmic randomized k-server on arbitrary metrics*, OpenAI Math Release, September 24, 2026, result family 110, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KServer.JointBudget.quota_bound` of [lean/OAI/Combinatorics/KServer/KServer/JointBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KServer/KServer/JointBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KServer.JointBudget`, with `open scoped BigOperators`, `open Finset`, `open JointExperiment JointAllocation HierarchicalQuota ActualCharges RankTracking`):
--
--   ```lean
--   lemma quota_bound {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
--       total (weight law hr) N (stepQuota s law hr hk R τ)≤
--         (12*τ*localConstant)*ActualCaps.ell k*total (weight law hr) N (stepKey s law hr)+
--         2*localConstant*ActualCaps.ell k*treeInventory (LevelKeys.Key Y k) k (fun d=>R/τ^d) L
--   ```
--
--   **Definitions.** The statement is written with `OAI.KServer.FiniteDistribution`, `OAI.KServer.ActualCaps.ell`, `OAI.KServer.ActualCharges.localConstant`, `OAI.KServer.ActualCharges.total`, `OAI.KServer.HierarchicalQuota.treeInventory`, `OAI.KServer.JointBudget.stepKey`, `OAI.KServer.JointBudget.stepQuota`, `OAI.KServer.JointExperiment.Atom`, `OAI.KServer.JointExperiment.Raw`, `OAI.KServer.JointExperiment.Tape`, `OAI.KServer.JointExperiment.levelTapeFintype`, `OAI.KServer.JointExperiment.rawWeight`, `OAI.KServer.JointExperiment.weight`, `OAI.KServer.LevelKeys.Alphabet`, `OAI.KServer.LevelKeys.Key`, `OAI.KServer.LevelKeys.Structure`, `OAI.KServer.LevelKeys.Tape`, `OAI.KServer.LevelKeys.Tier`, `OAI.KServer.LevelKeys.alphabetFintype` and `OAI.KServer.TierDyadic.index` (definitions bundle `OAIQ17Ks000` of this split); `OAI.KServer.Configuration` (the published bundle `Def_KServer`).
--
--   **Used by.** The proof of `OAI.KServer.main_theorem` of this split imports it.
-- source:
--   OpenAI, Squared-logarithmic randomized k-server on arbitrary metrics, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 110; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026/Squared-logarithmic-randomized-k-server-on-arbitrary-metrics-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KServer/KServer/JointBudget.lean (declaration OAI.KServer.JointBudget.quota_bound)

import Mathlib
import Definitions.Def_KServer
import Definitions.Def_OAIQ17Ks000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
namespace KServer.JointBudget
open JointExperiment JointAllocation HierarchicalQuota ActualCharges RankTracking
attribute [local instance] Classical.propDecidable Classical.decEq
variable {Y:Type} [MetricSpace Y] [Fintype Y] {k H L:ℕ} [NeZero k]
variable (s:Configuration k Y) (law:FiniteDistribution (Fin H→Y))
variable {r:Fin L→ℝ} (hr:∀ d,0 < r d) (hk:1≤(k:ℝ))

lemma quota_bound {R τ:ℝ} (hR:0≤R) (hτ:2≤τ) (hrad:∀ d,r d=R/τ^(d.val+1)) (N:ℕ):
    total (weight law hr) N (stepQuota s law hr hk R τ)≤
      (12*τ*localConstant)*ActualCaps.ell k*total (weight law hr) N (stepKey s law hr)+
      2*localConstant*ActualCaps.ell k*treeInventory (LevelKeys.Key Y k) k (fun d=>R/τ^d) L:= by
  sorry

end KServer.JointBudget

end

end OAI
end
