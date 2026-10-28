-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Marking_eventually_high_ordered
-- name    : OAI.SharpLogRamsey.Marking.eventually_high_ordered
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:25:04.487955+00:00
-- url     : https://prove2.me/theorems/88d8424e-1384-4227-b611-0bdf1308deae
-- title:
--   OAI.SharpLogRamsey.Marking.eventually_high_ordered: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Marking.eventually_high_ordered` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/HighRankOrdered.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/HighRankOrdered.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Marking`, with `open Finset Real Filter Selection Selection.Windows ActualHighRank HighRankBudgets`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_high_ordered {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
--       (C c : ℝ) (hC : 0≤C) (hc : 0 < c) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
--         log (Nat.card K:ℝ)=σ →
--         ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
--           (F : Ω→Fin (4*(n+k))→ProjectivePair (K:=K) (V:=Fin (d+1)→K))
--           (S : Θ→Fin (4*(n+k))→Finset (ProjectivePair (K:=K) (V:=Fin (d+1)→K)))
--           (D J budget gap : ℝ) (r r' : Fin (d+1)), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
--         (∀ ω,p.mass ω≠0→∀ i,F ω i∈S (θ ω) i) →
--         (∀ z i,log (S z i).card≤J) →
--         (∀ ω,p.mass ω≠0→∀ i,Incidence.Incident (F ω i).1 (F ω i).2) →
--         (∀ ω,p.mass ω≠0→ScanConsistent ((List.ofFn (F ω)).map toScan)) →
--         (∀ ω,p.mass ω≠0→∀ i,ValidSlotClass d gap (S (θ ω) i) (.inr (r,r'))) →
--         (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
--         (∑ z : Θ,(p.map θ).mass z*(((4*(n+k):ℕ):ℝ)*J-
--             entropy ((p.cond θ z).map F)))≤budget →
--         budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
--         c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
--         Nonempty (StreamReplacement p F Fin.val ((n+k)/2)
--           (fun code=>(rawDomain (h:=rawRows σ η) code r.val (rawThreshold σ η)).map
--             (Equiv.prodComm _ _).toEmbedding)
--           (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
--           (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualHighRank.StreamReplacement`, `OAI.SharpLogRamsey.ActualHighRank.highPrefactor`, `OAI.SharpLogRamsey.ActualHighRank.rawDomain`, `OAI.SharpLogRamsey.ActualHighRank.rawRows`, `OAI.SharpLogRamsey.ActualHighRank.rawThreshold`, `OAI.SharpLogRamsey.HighRankBudgets.beta`, `OAI.SharpLogRamsey.HighRankBudgets.scaleK`, `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.Marking.Points`, `OAI.SharpLogRamsey.Marking.ProjectivePair`, `OAI.SharpLogRamsey.Marking.ScanConsistent`, `OAI.SharpLogRamsey.Marking.ScanFlag`, `OAI.SharpLogRamsey.Marking.ValidSlotClass`, `OAI.SharpLogRamsey.Marking.toScan`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.Selection.entropy`, `OAI.SharpLogRamsey.Selection.Law.cond` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_3` and `OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_4` (definitions bundle `OAIQ045S001` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_class_step` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Marking/HighRankOrdered.lean (declaration OAI.SharpLogRamsey.Marking.eventually_high_ordered)

import Mathlib
import Definitions.Def_OAIQ045S000
import Definitions.Def_OAIQ045S001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset Real Filter Selection Selection.Windows ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_3
attribute [local instance] OAI.SharpLogRamsey.Marking.flat_ActualHighRankOrdered_4
theorem eventually_high_ordered {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d)
    (C c : ℝ) (hC : 0≤C) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (n k : ℕ), 2≤n → 0<k → k≤n → ∀ (p : Law Ω) (θ : Ω→Θ)
        (F : Ω→Fin (4*(n+k))→ProjectivePair (K:=K) (V:=Fin (d+1)→K))
        (S : Θ→Fin (4*(n+k))→Finset (ProjectivePair (K:=K) (V:=Fin (d+1)→K)))
        (D J budget gap : ℝ) (r r' : Fin (d+1)), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      (∀ ω,p.mass ω≠0→∀ i,F ω i∈S (θ ω) i) →
      (∀ z i,log (S z i).card≤J) →
      (∀ ω,p.mass ω≠0→∀ i,Incidence.Incident (F ω i).1 (F ω i).2) →
      (∀ ω,p.mass ω≠0→ScanConsistent ((List.ofFn (F ω)).map toScan)) →
      (∀ ω,p.mass ω≠0→∀ i,ValidSlotClass d gap (S (θ ω) i) (.inr (r,r'))) →
      (∀ z i,((S z i).card:ℝ)≤64*(Nat.card K:ℝ)^d) →
      (∑ z : Θ,(p.map θ).mass z*(((4*(n+k):ℕ):ℝ)*J-
          entropy ((p.cond θ z).map F)))≤budget →
      budget≤C*((2*(n+k):ℕ):ℝ)*D*σ^(-beta η) →
      c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
      Nonempty (StreamReplacement p F Fin.val ((n+k)/2)
        (fun code=>(rawDomain (h:=rawRows σ η) code r.val (rawThreshold σ η)).map
          (Equiv.prodComm _ _).toEmbedding)
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  sorry
end
end SharpLogRamsey.Marking

end

end OAI
end
