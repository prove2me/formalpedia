-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_class_step
-- name    : OAI.SharpLogRamsey.Marking.eventually_class_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:28:15.373266+00:00
-- url     : https://prove2.me/theorems/eef7798d-5c7c-4ecb-be80-da597af9f59c
-- title:
--   OAI.SharpLogRamsey.Marking.eventually_class_step: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Marking.eventually_class_step` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/ClassStep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/ClassStep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Marking`, with `open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_class_step (i : ℕ) (η c C C0 : ℝ)
--       (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
--       ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
--         (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
--         (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
--         (D J M budget : ℝ) (R : ℕ) (cl : SlotClass (i+3)),
--         Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
--         ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
--         (∀ z j,log (S z j).card ≤ J) →
--         (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
--         (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
--         (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
--         (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) cl) →
--         (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
--         (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
--         budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
--         (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
--           ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
--             orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
--         ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
--           Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
--             (D*σ^(-η/3)*(m:ℝ)) 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.Marking.CovectorPair`, `OAI.SharpLogRamsey.Marking.Points`, `OAI.SharpLogRamsey.Marking.ProjectivePair`, `OAI.SharpLogRamsey.Marking.ScanConsistent`, `OAI.SharpLogRamsey.Marking.ScanFlag`, `OAI.SharpLogRamsey.Marking.SlotClass`, `OAI.SharpLogRamsey.Marking.ValidSlotClass`, `OAI.SharpLogRamsey.Marking.toScan`, `OAI.SharpLogRamsey.Selection.ContextOutput`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.Selection.entropy`, `OAI.SharpLogRamsey.SourceScales.Admissible`, `OAI.SharpLogRamsey.SourceScales.beta`, `OAI.SharpLogRamsey.SourceScales.scaleKstar`, `OAI.SharpLogRamsey.Selection.Law.cond` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Marking.stepDualProjective`, `OAI.SharpLogRamsey.Marking.stepProjective` and `OAI.SharpLogRamsey.Selection.orthogonalRectangle` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Marking.covectorTuple` and `OAI.SharpLogRamsey.Marking.stepPrefactor` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_tracked_step` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/ClassStep.lean (declaration OAI.SharpLogRamsey.Marking.eventually_class_step)

import Mathlib
import Definitions.Def_OAIQ045S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.stepProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.stepDualProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.stepDoubleProjective
theorem eventually_class_step (i : ℕ) (η c C C0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hC : 0 < C) (hC0 : 0 < C0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω Θ : Type) [Fintype Ω] [Fintype Θ] (m : ℕ) (p : Law Ω) (θ : Ω→Θ)
      (F : Ω→Fin m→ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q))
      (S : Θ→Fin m→Finset (ProjectivePair (K:=ZMod q) (V:=Fin (i+4)→ZMod q)))
      (D J M budget : ℝ) (R : ℕ) (cl : SlotClass (i+3)),
      Admissible σ η D R → c*(q:ℝ)*σ^(1+η) ≤ m → (m:ℝ) ≤ C*q*σ^(1+η) →
      ((i+3:ℕ):ℝ)*σ ≤ J → 0 ≤ M → M ≤ C0*σ →
      (∀ z j,log (S z j).card ≤ J) →
      (∀ x,p.mass x≠0→∀ j,F x j∈S (θ x) j) →
      (∀ x,p.mass x≠0→∀ j,Incidence.Incident (F x j).1 (F x j).2) →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (F x)).map toScan)) →
      (∀ x,p.mass x≠0→∀ j,ValidSlotClass (i+3) (scaleKstar σ η D) (S (θ x) j) cl) →
      (∀ z j,((S z j).card:ℝ) ≤ 64*(q:ℝ)^(i+3)) →
      (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map F))) ≤ budget →
      budget ≤ C0*(m:ℝ)*D*σ^(-beta η) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin m=>covectorTuple (F x) j∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M) →
      ∃ m' : ℕ, (m:ℝ)/64 ≤ m' ∧
        Nonempty (ContextOutput p F m' (stepPrefactor (i+3)*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η D))
          (D*σ^(-η/3)*(m:ℝ)) 4) := by
  sorry
end
end SharpLogRamsey.Marking

end

end OAI
end
