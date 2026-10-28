-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_open_decoder
-- name    : OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:27:42.608487+00:00
-- url     : https://prove2.me/theorems/2642baab-2b26-4c95-86fa-91ee9832850c
-- title:
--   OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/UniformOpen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/UniformOpen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Selection.Windows`, with `open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_open_decoder (d : ℕ) (η C A loss : ℝ)
--       (hη : 0<η) (hC : 0<C) (hloss : 0<loss) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
--         [FiniteDimensional K V]
--         [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
--         [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
--         ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
--         ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
--         let b:=16*scaleKstar σ η D
--         let τ:=σ^(-100*beta η)
--         ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
--           (hτ : 0≤τ) (hτsmall : τ≤1/40000)
--           (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
--           (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
--           (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
--           (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
--           (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
--           (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
--           (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
--           (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
--           (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
--             (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
--           (∀ ω,p.mass ω≠0→∀ i,
--             (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
--             (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
--             ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
--           (∀ ω,p.mass ω≠0→∀ i,OpenBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
--           ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
--             (z : (model w n k p θ G t).FreshHistory),
--             ((model w n k p θ G t).freshLaw hp).mass z≠0 →
--             ∀ fallback : Fin w,
--             let M:=model w n k p θ G t
--             let q:=M.tupleLaw z.1
--             let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
--             let c:=fun (_ _ : M.Index z.1)=>(0:NNReal)
--             let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
--             let live:=(univ\badWindows (M.representative z) bad).filter
--               (fun i=>u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
--                 u z.1.1 (M.origin z.1 (M.representative z (i,true)))≤ scaleKstar σ η D)
--             ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
--               (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
--                 ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
--                 (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
--                   (fun i=>book.chronoChoose hdim hτ hτsmall (e.supports ω i))
--                   (fun _=>chronoRead b)
--                   (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
--                   (liveTree live fallback) (univ,univ)).length))≤
--                 (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*loss
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Banks`, `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.Code`, `OAI.SharpLogRamsey.ActualPivot.Realization`, `OAI.SharpLogRamsey.ActualPivot.banksLaw`, `OAI.SharpLogRamsey.ActualPivot.chronoRead`, `OAI.SharpLogRamsey.ChronologicalTree.liveTree`, `OAI.SharpLogRamsey.FreshExecution.fullOutput`, `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.PublicTables.piLaw`, `OAI.SharpLogRamsey.ReciprocalBands.OpenBand`, `OAI.SharpLogRamsey.Selection.ExposureModel`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.SourceScales.beta`, `OAI.SharpLogRamsey.SourceScales.scaleKstar`, `OAI.SharpLogRamsey.ActualPivot.Book.chronoChoose`, `OAI.SharpLogRamsey.PublicTables.Law`, `OAI.SharpLogRamsey.Selection.Law.cond` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Selection.Windows.Block`, `OAI.SharpLogRamsey.Selection.Windows.Slot`, `OAI.SharpLogRamsey.Selection.Windows.badWindows`, `OAI.SharpLogRamsey.Selection.Windows.embedding`, `OAI.SharpLogRamsey.Selection.Windows.owner`, `OAI.SharpLogRamsey.Selection.Windows.position`, `OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenBlockDec` and `OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenFinDec` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.Selection.badIndices`, `OAI.SharpLogRamsey.Selection.ExposureModel.FreshHistory`, `OAI.SharpLogRamsey.Selection.ExposureModel.atRound`, `OAI.SharpLogRamsey.Selection.ExposureModel.freshLaw`, `OAI.SharpLogRamsey.Selection.ExposureModel.representative`, `OAI.SharpLogRamsey.Selection.Windows.goodMiddle`, `OAI.SharpLogRamsey.Selection.Windows.goodTarget`, `OAI.SharpLogRamsey.Selection.Windows.model` and `OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenBanks` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Selection.Windows.eventually_open_output` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/UniformOpen.lean (declaration OAI.SharpLogRamsey.Selection.Windows.eventually_open_decoder)

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
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenBanks
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenFinDec
attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.uniformIntOpenBlockDec
theorem eventually_open_decoder (d : ℕ) (η C A loss : ℝ)
    (hη : 0<η) (hC : 0<C) (hloss : 0<loss) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      ∀ (hdim : Module.finrank K V=d+3), log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (hτ : 0≤τ) (hτsmall : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J : ℝ),
        (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,OpenBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        ∀ (t : Fin k) (hp : ∀ z,0<(model w n k p θ G t).remaining z)
          (z : (model w n k p θ G t).FreshHistory),
          ((model w n k p θ G t).freshLaw hp).mass z≠0 →
          ∀ fallback : Fin w,
          let M:=model w n k p θ G t
          let q:=M.tupleLaw z.1
          let a:=σ^(-2000*beta η)/(Nat.card K:ℝ)
          let c:=fun (_ _ : M.Index z.1)=>(0:NNReal)
          let bad:=badIndices q (M.embedding z.1) (M.owner z.1) c J (D*σ^beta η) a z.2
          let live:=(univ\badWindows (M.representative z) bad).filter
            (fun i=>u z.1.1 (M.origin z.1 (M.representative z (i,false)))-
              u z.1.1 (M.origin z.1 (M.representative z (i,true)))≤ scaleKstar σ η D)
          ∃ e : Realization (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) q,
            (∑ tab,(PublicTables.piLaw (fun _ : Fin w=>banksLaw (K:=K) (V:=V) b)).mass tab*
              ∑ ω,e.μ.mass ω*((∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))-
              (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
                (fun i=>book.chronoChoose hdim hτ hτsmall (e.supports ω i))
                (fun _=>chronoRead b)
                (fun i=>List.ofFn (fun j=>e.source ω (goodTarget w n k p θ G t z bad i j))) tab
                (liveTree live fallback) (univ,univ)).length))≤
              (∑ i∈live,((goodMiddle w n k p θ G t z bad i).card:ℝ))*loss := by
  sorry
end
end SharpLogRamsey.Selection.Windows

end

end OAI
end
