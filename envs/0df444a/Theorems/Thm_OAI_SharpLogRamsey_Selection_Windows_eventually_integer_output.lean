-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_Selection_Windows_eventually_integer_output
-- name    : OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:25:19.228691+00:00
-- url     : https://prove2.me/theorems/2ec7d7ac-5bd2-4cad-9858-054d95d03112
-- title:
--   OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/IntegerOutput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/IntegerOutput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.Selection.Windows`, with `open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales`, `open scoped Classical BigOperators Topology`):
--
--   ```lean
--   theorem eventually_integer_output (d : ℕ) (η C A C0 c : ℝ)
--       (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0 < c) :
--       ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
--         [FiniteDimensional K V]
--         [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
--         [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
--         Module.finrank K V=d+3 → log (Nat.card K)=σ →
--         ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
--         let b:=16*scaleKstar σ η D
--         let τ:=σ^(-100*beta η)
--         ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
--           (_ : 0≤b) (_ : 0≤H) (_ : 4≤P) (_ : b+log 1000000≤P)
--           (_ : 0≤τ) (_ : τ≤1/40000)
--           (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
--           (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
--           (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
--           (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
--           (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
--           2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
--           (∀ z i,log (S z i).card≤J) →
--           (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
--           (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
--           (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
--             (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
--           (∀ ω,p.mass ω≠0→∀ i,
--             (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
--             (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
--             ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
--           (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
--           (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
--             ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
--           (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
--             entropy ((p.cond θ z).map G)))≤budget →
--           budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) → M≤C0*σ →
--           c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
--           c*(Nat.card K:ℝ)*σ^(1+η/2)≤n →
--           Fin w →
--           Nonempty (ContextOutput p (fun ω=>flattenTuple (G ω)) (w*(n+k))
--             (8000000*(Nat.card K:ℝ)^(d+2)*exp b)
--             (reciprocalOutputCost (K:=K) (V:=V) (I:=Fin w) (d:=d) (b:=b) (P:=P) (H:=H)
--               w (Nat.log 2 w+1) (2*(n+k))) 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.reciprocalOutputCost`, `OAI.SharpLogRamsey.ReciprocalBands.IntegerBand`, `OAI.SharpLogRamsey.Selection.ContextOutput`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.Selection.entropy`, `OAI.SharpLogRamsey.SourceScales.beta`, `OAI.SharpLogRamsey.SourceScales.scaleKstar`, `OAI.SharpLogRamsey.Selection.Law.cond` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split); `OAI.SharpLogRamsey.Selection.orthogonalRectangle`, `OAI.SharpLogRamsey.Selection.Windows.Slot`, `OAI.SharpLogRamsey.Selection.Windows.flattenTuple`, `OAI.SharpLogRamsey.Selection.Windows.outputSlotDec` and `OAI.SharpLogRamsey.Selection.Windows.position` (definitions bundle `OAIQ045S001` of this split).
--
--   **Used by.** The proof of `OAI.SharpLogRamsey.Marking.eventually_class_step` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Windows/IntegerOutput.lean (declaration OAI.SharpLogRamsey.Selection.Windows.eventually_integer_output)

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
namespace SharpLogRamsey.Selection.Windows
open Finset Real Filter ExposureModel ChronologicalTree FreshExecution TreeDecoder BinaryTree ActualPivot ReciprocalBands SourceScales
open scoped Classical BigOperators Topology
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] {b : ℝ}

attribute [local instance] OAI.SharpLogRamsey.Selection.Windows.outputSlotDec
theorem eventually_integer_output (d : ℕ) (η C A C0 c : ℝ)
    (hη : 0<η) (hC : 0<C) (hC0 : 0≤C0) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop, ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V]
      [FiniteDimensional K V]
      [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
      [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))],
      Module.finrank K V=d+3 → log (Nat.card K)=σ →
      ∀ D P H : ℝ, σ^beta η≤D → D≤σ^(1-η/2) →
      let b:=16*scaleKstar σ η D
      let τ:=σ^(-100*beta η)
      ∀ (_ : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
        (_ : 0≤b) (_ : 0≤H) (_ : 4≤P) (_ : b+log 1000000≤P)
        (_ : 0≤τ) (_ : τ≤1/40000)
        (Ω Θ : Type) [Fintype Ω] [Fintype Θ]
        (w n k : ℕ) (p : Law Ω) (θ : Ω→Θ)
        (G : Ω→Slot w (n+k)→Projectivization K (Module.Dual K V)×Projectivization K V)
        (S : Θ→Slot w (n+k)→Finset (Projectivization K (Module.Dual K V)×Projectivization K V))
        (u : Θ→Slot w (n+k)→ℝ) (r : ℕ) (J M budget : ℝ),
        2≤n → 0<k → k≤n → (w:ℝ)≤C*σ^A → r≤d+3 → ((d+2:ℕ):ℝ)*σ≤J → 0≤M →
        (∀ z i,log (S z i).card≤J) →
        (∀ ω,p.mass ω≠0→∀ i,G ω i∈S (θ ω) i) →
        (∀ ω,p.mass ω≠0→∀ i,(G ω i).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i j,position i<position j→
          (G ω i).1.rep (G ω j).2.rep=0 → (G ω j).1.rep (G ω i).2.rep=0) →
        (∀ ω,p.mass ω≠0→∀ i,
          (((S (θ ω) i).image Prod.fst).card:ℝ)≤1024*exp (((d+3:ℕ):ℝ)*σ-u (θ ω) i) ∧
          (((S (θ ω) i).image Prod.snd).card:ℝ)≤1024*exp (u (θ ω) i) ∧
          ((S (θ ω) i).card:ℝ)≤64*(Nat.card K:ℝ)^(d+2)) →
        (∀ ω,p.mass ω≠0→∀ i,IntegerBand r σ (scaleKstar σ η D) (u (θ ω) i)) →
        (∀ ω,p.mass ω≠0→∀ W : Submodule K V,
          ((univ.filter (fun i=>G ω i∈orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ)≤M) →
        (∑ z,(p.map θ).mass z*((Fintype.card (Slot w (n+k)):ℝ)*J-
          entropy ((p.cond θ z).map G)))≤budget →
        budget≤C0*(w*(2*(n+k)):ℝ)*D*σ^(-beta η) → M≤C0*σ →
        c*(Nat.card K:ℝ)*D*σ^(3000*beta η)≤k →
        c*(Nat.card K:ℝ)*σ^(1+η/2)≤n →
        Fin w →
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
