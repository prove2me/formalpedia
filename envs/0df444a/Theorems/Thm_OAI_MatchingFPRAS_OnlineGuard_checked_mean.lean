-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineGuard_checked_mean
-- name    : OAI.MatchingFPRAS.OnlineGuard.checked_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:06:03.9628+00:00
-- url     : https://prove2.me/theorems/cdfd177a-57ee-48f8-bf8b-171c29393483
-- title:
--   OAI.MatchingFPRAS.OnlineGuard.checked_mean: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineGuard.checked_mean` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineGuardLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineGuardLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineGuard`, with `open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage`, `open Transport UnitRefresh Enlargement Variation TreeTyped.Numbered`, `open scoped Classical`):
--
--   ```lean
--   lemma checked_mean (p : Trial.Parameters G) (x : (FiniteTrial.layers p p.K le_rfl).Ω) (h : Fraction→ℚ) :
--       (checked (OnlineTrial.represent p (FiniteTrial.layers p p.K le_rfl) x)).mean h=
--         qaverage (fun b=>h (TreeFraction.repr (FiniteTrial.guardedOutput p ⟨x,((FiniteTrial.layers p p.K le_rfl).state x).drawGuard p b⟩)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeFraction.Fraction` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.PhysicalStream.qaverage` and `OAI.MatchingFPRAS.PhysicalStream.Experiment.mean` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.TreeFraction.repr` and `OAI.MatchingFPRAS.Trial.Parameters` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.FiniteTrial.GuardSamples`, `OAI.MatchingFPRAS.FiniteTrial.guardBits`, `OAI.MatchingFPRAS.FiniteTrial.guardedOutput`, `OAI.MatchingFPRAS.FiniteTrial.layers`, `OAI.MatchingFPRAS.OnlineGuard.checked`, `OAI.MatchingFPRAS.OnlineTrial.represent`, `OAI.MatchingFPRAS.FiniteTrial.Layer` and `OAI.MatchingFPRAS.FiniteTrial.ScaleState.drawGuard` (definitions bundle `OAIQ051M004` of this split); `OAI.MatchingFPRAS.GraphInput` (the published bundle `Def_MatchingFPRAS`).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.LiteralAlgorithm.compute_mean` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineGuardLaw.lean (declaration OAI.MatchingFPRAS.OnlineGuard.checked_mean)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGuard
open PhysicalStream TreeTyped TreeFraction ExecutableSource ExecutableScaling OnlineSchedule OnlineStage
open Transport UnitRefresh Enlargement Variation TreeTyped.Numbered
open scoped Classical

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma checked_mean (p : Trial.Parameters G) (x : (FiniteTrial.layers p p.K le_rfl).Ω) (h : Fraction→ℚ) :
    (checked (OnlineTrial.represent p (FiniteTrial.layers p p.K le_rfl) x)).mean h=
      qaverage (fun b=>h (TreeFraction.repr (FiniteTrial.guardedOutput p ⟨x,((FiniteTrial.layers p p.K le_rfl).state x).drawGuard p b⟩))) := by
  sorry

end MatchingFPRAS.OnlineGuard

end OAI
end
