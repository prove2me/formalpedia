-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_open_population_realization
-- name    : OAI.SharpLogRamsey.Selection.Windows.open_population_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:31:27.407809+00:00
-- url     : https://prove2.me/theorems/7b08d408-e59a-474a-86d9-380875214967
-- title:
--   OAI.SharpLogRamsey.Selection.Windows.open_population_realization: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Selection.Windows.open_population_realization` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/OpenRealization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/OpenRealization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Selection.Windows`, with `open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem open_population_realization
--       (hdim : Module.finrank K V=d+3)
--       (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
--       (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
--       (r : ℕ) (hr : r≤d+3) (κ gap J D a δ : ℝ)
--       (u : (M).Index z.1→ℝ)
--       (hband : ∀ i,OpenBand r (log (Nat.card K)) gap (u i))
--       (hsmall : log 1024+3*κ<gap) (hκ : log (200/97)≤κ)
--       (hbudget : gap+2*κ+log 4≤b) (ha : 0≤a)
--       (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
--         (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
--       (hf : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0)
--       (fallback : Fin w)
--       (hsupp :
--         let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
--         let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
--         ∀ i,i∉bad→
--         let qi:=(q).marginal i
--         let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
--         let MB:=1024*exp (u i)
--         let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
--         Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
--         Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ) ∧
--         qi.fst.event (univ.filter (fun x=>¬goodFirst qi MA L κ (1/50) x))≤δ ∧
--         qi.snd.event (univ.filter (fun x=>¬goodSecond qi MB L κ (1/50) x))≤δ) :
--       let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
--       let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
--       let live:=(univ\badWindows ((M).representative z) bad).filter
--         (fun i=>u ((M).representative z (i,false))-u ((M).representative z (i,true))≤gap)
--       ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
--         (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
--           ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
--           (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
--             (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
--             (fun _=>chronoRead b)
--             (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
--             (liveTree live fallback) (univ,univ)).length))≤
--           (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
--             treeError (Nat.card K) τ (liveTree live fallback).height
--               ((20000*((d:ℝ)+3)^2)*a) ((20000*((d:ℝ)+3)^2)*a)
--               ((20000*((d:ℝ)+3)^2)*a) δ δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Banks`, `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.Code`, `OAI.SharpLogRamsey.ActualPivot.Realization`, `OAI.SharpLogRamsey.ActualPivot.banksLaw`, `OAI.SharpLogRamsey.ActualPivot.chronoRead`, `OAI.SharpLogRamsey.ActualPivot.treeError`, `OAI.SharpLogRamsey.ChronologicalTree.liveTree`, `OAI.SharpLogRamsey.FreshExecution.fullOutput`, `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.PublicTables.piLaw`, `OAI.SharpLogRamsey.ReciprocalBands.OpenBand`, `OAI.SharpLogRamsey.Selection.AuxiliarySupport`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.ActualPivot.Book.chronoChoose`, `OAI.SharpLogRamsey.PublicTables.Law`, `OAI.SharpLogRamsey.Selection.ExposureModel`, `OAI.SharpLogRamsey.Selection.Law.event`, `OAI.SharpLogRamsey.Selection.Law.fst`, `OAI.SharpLogRamsey.Selection.Law.marginal` and `OAI.SharpLogRamsey.Selection.Law.snd` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Selection.Windows.Block`, `OAI.SharpLogRamsey.Selection.Windows.Slot`, `OAI.SharpLogRamsey.Selection.Windows.badWindows`, `OAI.SharpLogRamsey.Selection.Windows.openBlockDec`, `OAI.SharpLogRamsey.Selection.Windows.openDec` and `OAI.SharpLogRamsey.Selection.Windows.position` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Selection.badIndices`, `OAI.SharpLogRamsey.Selection.goodFirst`, `OAI.SharpLogRamsey.Selection.goodSecond`, `OAI.SharpLogRamsey.Selection.ExposureModel.FreshHistory`, `OAI.SharpLogRamsey.Selection.ExposureModel.freshLaw`, `OAI.SharpLogRamsey.Selection.ExposureModel.representative`, `OAI.SharpLogRamsey.Selection.Windows.goodMiddle`, `OAI.SharpLogRamsey.Selection.Windows.goodTarget`, `OAI.SharpLogRamsey.Selection.Windows.model` and `OAI.SharpLogRamsey.Selection.Windows.openBanks` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/OpenRealization.lean (declaration OAI.SharpLogRamsey.Selection.Windows.open_population_realization)

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
open Finset Real ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V Ω Θ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype Ω] [Fintype Θ] {d : ℕ} {b τ P H : ℝ}
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openDec
variable (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
  (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V) (t : Fin k)
local instance openSlotDec_r41ee31_1 : DecidableEq (Slot w (n+k)) :=
  @instDecidableEqProd (Fin w) (Fin (4*(n+k))) (@instDecidableEqFin w) (@instDecidableEqFin (4*(n+k)))
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openBlockDec
variable (hp : ∀ z,0<(model w n k p θ G t).remaining z)
  (z : (model w n k p θ G t).FreshHistory)
  (hz : ((model w n k p θ G t).freshLaw hp).mass z≠0)
local notation "M" => model w n k p θ G t
local notation "q" => ExposureModel.tupleLaw (model w n k p θ G t) (Sigma.fst z)

include hp hz

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.openBanks
theorem open_population_realization
    (hdim : Module.finrank K V=d+3)
    (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
    (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)
    (r : ℕ) (hr : r≤d+3) (κ gap J D a δ : ℝ)
    (u : (M).Index z.1→ℝ)
    (hband : ∀ i,OpenBand r (log (Nat.card K)) gap (u i))
    (hsmall : log 1024+3*κ<gap) (hκ : log (200/97)≤κ)
    (hbudget : gap+2*κ+log 4≤b) (ha : 0≤a)
    (hcon : ∀ ω,p.mass ω≠0→∀ i j,position i<position j→
      (G ω i).1.rep (G ω j).2.rep=0→(G ω j).1.rep (G ω i).2.rep=0)
    (hf : ∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0)
    (fallback : Fin w)
    (hsupp :
      let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
      let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
      ∀ i,i∉bad→
      let qi:=(q).marginal i
      let MA:=1024*exp (((d+3:ℕ):ℝ)*log (Nat.card K)-u i)
      let MB:=1024*exp (u i)
      let L:=((d+2:ℕ):ℝ)*log (Nat.card K)
      Nonempty (AuxiliarySupport qi.fst (univ.filter (goodFirst qi MA L κ (1/50))) MA κ) ∧
      Nonempty (AuxiliarySupport qi.snd (univ.filter (goodSecond qi MB L κ (1/50))) MB κ) ∧
      qi.fst.event (univ.filter (fun x=>¬goodFirst qi MA L κ (1/50) x))≤δ ∧
      qi.snd.event (univ.filter (fun x=>¬goodSecond qi MB L κ (1/50) x))≤δ) :
    let c:=fun (_ _ : (M).Index z.1)=> (0 : NNReal)
    let bad:=badIndices q ((M).embedding z.1) ((M).owner z.1) c J D a z.2
    let live:=(univ\badWindows ((M).representative z) bad).filter
      (fun i=>u ((M).representative z (i,false))-u ((M).representative z (i,true))≤gap)
    ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
      (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
        ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b)
          (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
          (liveTree live fallback) (univ,univ)).length))≤
        (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*
          treeError (Nat.card K) τ (liveTree live fallback).height
            ((20000*((d:ℝ)+3)^2)*a) ((20000*((d:ℝ)+3)^2)*a)
            ((20000*((d:ℝ)+3)^2)*a) δ δ := by
  sorry
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end
