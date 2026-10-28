-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_prepared_context_of_mean
-- name    : OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:29:45.037859+00:00
-- url     : https://prove2.me/theorems/b9b1d702-9c21-4013-a900-1fe13a83e80c
-- title:
--   OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Execution/PreparedOutput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Execution/PreparedOutput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Selection.Windows`, with `open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem prepared_context_of_mean (hdim : Module.finrank K V=d+3)
--       (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
--       (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
--       (hτ : 0≤τ) (hτsmall : τ≤1/40000) (hn : 0<n)
--       (hmean : (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
--         ∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*((w*(2*(n+k)):ℝ)-
--         (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
--           (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
--           (fun _=>chronoRead b) (preparedTargets w n k p θ G t hp e bad ω.1) tab
--           (preparedTree w n k p θ G t hp e live fallback ω.1) (univ,univ)).length))≤
--         (w*(2*(n+k)):ℝ)/4) :
--       Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
--         (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
--         (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
--           w (Nat.log 2 w+1) (2*(n+k))) 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Banks`, `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.Code`, `OAI.SharpLogRamsey.ActualPivot.Flag`, `OAI.SharpLogRamsey.ActualPivot.Realization`, `OAI.SharpLogRamsey.ActualPivot.banksLaw`, `OAI.SharpLogRamsey.ActualPivot.chronoRead`, `OAI.SharpLogRamsey.ActualPivot.reciprocalOutputCost`, `OAI.SharpLogRamsey.FreshExecution.fullOutput`, `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.PublicTables.piLaw`, `OAI.SharpLogRamsey.Selection.ContextOutput`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.ActualPivot.Book.chronoChoose`, `OAI.SharpLogRamsey.PublicTables.Law`, `OAI.SharpLogRamsey.Selection.ExposureModel` and `OAI.SharpLogRamsey.Selection.Law.sigma` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Selection.Windows.Block`, `OAI.SharpLogRamsey.Selection.Windows.Slot`, `OAI.SharpLogRamsey.Selection.Windows.flattenTuple` and `OAI.SharpLogRamsey.Selection.Windows.prepOutFinDec` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Selection.ExposureModel.FreshHistory`, `OAI.SharpLogRamsey.Selection.ExposureModel.freshLaw`, `OAI.SharpLogRamsey.Selection.Windows.PositiveHistory`, `OAI.SharpLogRamsey.Selection.Windows.attachedPrepared`, `OAI.SharpLogRamsey.Selection.Windows.mixedPrepared`, `OAI.SharpLogRamsey.Selection.Windows.model`, `OAI.SharpLogRamsey.Selection.Windows.prepOutBanks`, `OAI.SharpLogRamsey.Selection.Windows.preparedTargets` and `OAI.SharpLogRamsey.Selection.Windows.preparedTree` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output` and `OAI.SharpLogRamsey.Selection.Windows.eventually_open_output` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Execution/PreparedOutput.lean (declaration OAI.SharpLogRamsey.Selection.Windows.prepared_context_of_mean)

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
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.prepOutFinDec
local instance prepOutBlockDec_r7c4326_1 (w : ℕ) : DecidableEq (Block w) := Classical.decEq _
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→ActualPivot.Flag (K:=K) (V:=V)) (t : Fin k)
  (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (e : ∀ z : PositiveHistory w n k p θ G t hp,
    Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b)
      (ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst (Subtype.val z))))
  (bad : ∀ z : (model w n k p θ G t).FreshHistory,Finset ((model w n k p θ G t).Index z.1))
  (live : (model w n k p θ G t).FreshHistory→Finset (Fin w)) (fallback : Fin w)

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.prepOutBanks
theorem prepared_context_of_mean (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hH : 0≤H) (hP : 4≤P) (haP : b+log 1000000≤P)
    (hτ : 0≤τ) (hτsmall : τ≤1/40000) (hn : 0<n)
    (hmean : (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
      ∑ ω,(attachedPrepared w n k p θ G t hp e).μ.mass ω*((w*(2*(n+k)):ℝ)-
      (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
        (fun i=>book.chronoChoose hdim hτ hτsmall ((e ω.1.1).supports ω.1.2 i))
        (fun _=>chronoRead b) (preparedTargets w n k p θ G t hp e bad ω.1) tab
        (preparedTree w n k p θ G t hp e live fallback ω.1) (univ,univ)).length))≤
      (w*(2*(n+k)):ℝ)/4) :
    Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
      (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
      (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
        w (Nat.log 2 w+1) (2*(n+k))) 2) := by
  sorry
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end
