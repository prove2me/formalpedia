-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_tracked_step
-- name    : OAI.SharpLogRamsey.Marking.eventually_tracked_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:27:32.225166+00:00
-- url     : https://prove2.me/theorems/22995838-9055-4c42-93d0-9b908397e809
-- title:
--   OAI.SharpLogRamsey.Marking.eventually_tracked_step: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Marking.eventually_tracked_step` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/TrackedStep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/TrackedStep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Marking`, with `open Finset Real Filter Selection Selection.Windows ActualHighRank SourceScales`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_tracked_step (i : ℕ) (η c Lstar P M0 : ℝ)
--       (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hLs : 0 < Lstar)
--       (hP : 1 ≤ P) (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
--       ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
--         (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
--         (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
--         (Λ Δ L : ℝ) (R : ℕ),
--         0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
--         0 ≤ Λ → 0 ≤ Δ → 0 < L → L ≤ Lstar →
--         Admissible σ η (stageD σ η k Λ Δ) R →
--         (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
--         (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
--         (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
--         (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
--         (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
--           ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
--             orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
--         (e : ContextOutput p (fun x j=>flagPair (F x j)) m
--           (P*(q:ℝ)^(i+3)*exp Δ) Λ L) → c*(q:ℝ)*σ^(1+η) ≤ m →
--         ∃ m' : ℕ, (m:ℝ)/(256*classCount i) ≤ m' ∧
--           Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m'
--             (P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
--             (stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ)) ((4*classCount i)*L))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.Flag`, `OAI.SharpLogRamsey.flagFintype`, `OAI.SharpLogRamsey.flagPair`, `OAI.SharpLogRamsey.Marking.Points`, `OAI.SharpLogRamsey.Marking.ProjectivePair`, `OAI.SharpLogRamsey.Marking.ScanConsistent`, `OAI.SharpLogRamsey.Marking.ScanFlag`, `OAI.SharpLogRamsey.Marking.toScan`, `OAI.SharpLogRamsey.Selection.ContextOutput`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.SourceScales.Admissible`, `OAI.SharpLogRamsey.SourceScales.scaleKstar` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Marking.classCount`, `OAI.SharpLogRamsey.Marking.trackDualProjective`, `OAI.SharpLogRamsey.Marking.trackProjective`, `OAI.SharpLogRamsey.Selection.Occurs`, `OAI.SharpLogRamsey.Selection.orthogonalRectangle` and `OAI.SharpLogRamsey.Selection.reverseTuple` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Marking.stepPrefactor` and `OAI.SharpLogRamsey.SourceScales.stageD` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.LowerTransfer.prime_construction` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/TrackedStep.lean (declaration OAI.SharpLogRamsey.Marking.eventually_tracked_step)

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

attribute [local instance] OAI.SharpLogRamsey.Marking.trackProjective
attribute [local instance] OAI.SharpLogRamsey.Marking.trackDualProjective
theorem eventually_tracked_step (i : ℕ) (η c Lstar P M0 : ℝ)
    (hη : 0 < η) (hηu : η ≤ 1) (hc : 0 < c) (hLs : 0 < Lstar)
    (hP : 1 ≤ P) (hPs : stepPrefactor (i+3) ≤ P) (hM0 : 0 ≤ M0) :
    ∀ᶠ σ : ℝ in atTop, ∀ (q : ℕ) [Fact q.Prime], 3 ≤ q → exp σ=(q:ℝ) →
    ∀ (Ω : Type) [Fintype Ω] (N k m : ℕ) (p : Law Ω)
      (stream : Ω→Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (F : Ω→Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q))
      (Λ Δ L : ℝ) (R : ℕ),
      0 < k → k ≤ N → (k:ℝ) ≤ (q:ℝ)*σ^(1+η) →
      0 ≤ Λ → 0 ≤ Δ → 0 < L → L ≤ Lstar →
      Admissible σ η (stageD σ η k Λ Δ) R →
      (∀ g,(p.map stream).mass g ≤ 2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N) →
      (∀ x,p.mass x≠0→Occurs (F x) (stream x) ∨ Occurs (reverseTuple (F x)) (stream x)) →
      (N:ℝ) ≤ (q:ℝ)^(i+3)*σ →
      (∀ x,p.mass x≠0→ScanConsistent ((List.ofFn (fun j=>flagPair (F x j))).map toScan)) →
      (∀ x,p.mass x≠0→∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
        ((univ.filter (fun j : Fin k=>(flagPair (F x j)).swap∈
          orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤ M0*σ) →
      (e : ContextOutput p (fun x j=>flagPair (F x j)) m
        (P*(q:ℝ)^(i+3)*exp Δ) Λ L) → c*(q:ℝ)*σ^(1+η) ≤ m →
      ∃ m' : ℕ, (m:ℝ)/(256*classCount i) ≤ m' ∧
        Nonempty (ContextOutput p (fun x j=>flagPair (F x j)) m'
          (P*(q:ℝ)^(i+3)*exp (16*scaleKstar σ η (stageD σ η k Λ Δ)))
          (stageD σ η k Λ Δ*σ^(-η/3)*(k:ℝ)) ((4*classCount i)*L)) := by
  sorry
end
end SharpLogRamsey.Marking

end

end OAI
end
