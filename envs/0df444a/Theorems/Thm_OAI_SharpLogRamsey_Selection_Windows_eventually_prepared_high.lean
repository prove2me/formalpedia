-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_prepared_high
-- name    : OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:31:14.448935+00:00
-- url     : https://prove2.me/theorems/57494a7d-1395-486c-9680-5d8aa4b56074
-- title:
--   OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/HighRankPrepared.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/HighRankPrepared.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Selection.Windows`, with `open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_prepared_high {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
--         log (Nat.card K:ℝ)=σ →
--         ∀ (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
--           (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
--           (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
--           (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
--         2 ≤ r → r≤d → d+2 ≤ r+r' →
--         (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
--         (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
--         (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
--           (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
--         (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
--         ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
--           (z : (model w n k p θ G t).FreshHistory),
--           ((model w n k p θ G t).freshLaw hp).mass z≠0 →
--         ∀ i : Fin w,
--         let M:=model w n k p θ G t
--         let q:=M.tupleLaw z.1
--         let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
--         let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
--         M.representative z (i,false)∉bad →
--         0<(goodMiddle w n k p θ G t z bad i).card →
--         Nonempty (Replacement q (fun y j=>y (goodTarget w n k p θ G t z bad i j))
--           (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
--           (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
--           (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualHighRank.Caps`, `OAI.SharpLogRamsey.ActualHighRank.Replacement`, `OAI.SharpLogRamsey.ActualHighRank.highPrefactor`, `OAI.SharpLogRamsey.ActualHighRank.rawDomain`, `OAI.SharpLogRamsey.ActualHighRank.rawRows`, `OAI.SharpLogRamsey.ActualHighRank.rawThreshold`, `OAI.SharpLogRamsey.HighRankBudgets.beta`, `OAI.SharpLogRamsey.HighRankBudgets.scaleK`, `OAI.SharpLogRamsey.Selection.ExposureModel` and `OAI.SharpLogRamsey.Selection.Law` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Selection.Windows.Block`, `OAI.SharpLogRamsey.Selection.Windows.Slot`, `OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_1`, `OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_3`, `OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_4` and `OAI.SharpLogRamsey.Selection.Windows.position` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Selection.badIndices`, `OAI.SharpLogRamsey.Selection.ExposureModel.FreshHistory`, `OAI.SharpLogRamsey.Selection.ExposureModel.freshLaw`, `OAI.SharpLogRamsey.Selection.ExposureModel.representative`, `OAI.SharpLogRamsey.Selection.Windows.goodMiddle`, `OAI.SharpLogRamsey.Selection.Windows.goodTarget` and `OAI.SharpLogRamsey.Selection.Windows.model` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_high_ordered` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/HighRankPrepared.lean (declaration OAI.SharpLogRamsey.Selection.Windows.eventually_prepared_high)

import Mathlib
import Definitions.Def_OAIQ045S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ActualHighRank HighRankBudgets
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_1
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_3
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.flat_ActualHighRankPrepared_4
theorem eventually_prepared_high {η : ℝ} (hη : 0<η) (d : ℕ) (hd : 2≤d) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K Ω Θ : Type) [Field K] [Fintype K] [Fintype Ω] [Fintype Θ],
      log (Nat.card K:ℝ)=σ →
      ∀ (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K))
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K (Fin (d+1)→K))×Projectivization K (Fin (d+1)→K)))
        (D J : ℝ) (r r' : ℕ), σ^beta η≤D → D≤σ^(1-η/2) → (d:ℝ)*σ≤J →
      2 ≤ r → r≤d → d+2 ≤ r+r' →
      (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
      (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
        (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0) →
      (∀ ω,p.mass ω≠0→∀ i,Caps σ r r' (S (θ ω) i)) →
      ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
        (z : (model w n k p θ G t).FreshHistory),
        ((model w n k p θ G t).freshLaw hp).mass z≠0 →
      ∀ i : Fin w,
      let M:=model w n k p θ G t
      let q:=M.tupleLaw z.1
      let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
      let bad:=badIndices q (M.embedding z.1) (M.owner z.1) (fun _ _=>0) J (D*σ^beta η) a z.2
      M.representative z (i,false)∉bad →
      0<(goodMiddle w n k p θ G t z bad i).card →
      Nonempty (Replacement q (fun y j=>y (goodTarget w n k p θ G t z bad i j))
        (fun code=>rawDomain (h:=rawRows σ η) code r (rawThreshold σ η))
        (highPrefactor d*(Nat.card K:ℝ)^d*exp (((d:ℝ)+1)*scaleK σ η D))
        (4*(rawRows σ η:ℝ)*(log 2+(d:ℝ)*σ))) := by
  sorry

end
end SharpLogRamsey.Selection.Windows

end

end OAI
end
