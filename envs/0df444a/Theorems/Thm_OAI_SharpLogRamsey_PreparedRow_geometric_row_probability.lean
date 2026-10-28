-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_PreparedRow_geometric_row_probability
-- name    : OAI.SharpLogRamsey.PreparedRow.geometric_row_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:29:14.374213+00:00
-- url     : https://prove2.me/theorems/57e5f513-d816-42a9-b094-aeda89ed87d3
-- title:
--   OAI.SharpLogRamsey.PreparedRow.geometric_row_probability: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.PreparedRow.geometric_row_probability` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/TestActualRow.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/TestActualRow.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.PreparedRow`, with `open Finset MeasureTheory LearningRow`, `open scoped BigOperators Classical NNReal`):
--
--   ```lean
--   theorem geometric_row_probability
--       (n R p h : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
--       (S Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty) (hDa : Ds⊆Da)
--       (O : Projectivization K V→Finset (Projectivization K V))
--       (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
--       (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
--       (f : Projectivization K V→ℝ) (hf : ∀ x,f x≤1/25)
--       (B C bE δ u zmin W tS tA : ℝ)
--       (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
--       (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
--       (hB : Real.exp (3*((L:ℝ)*R))≤B)
--       (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
--       (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
--       (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
--       (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
--       (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
--       (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-f x))*((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
--       (T : Finset I) (a : I→ℝ)
--       (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (O x) x c L (pencil x\E) (f x) B C T a)
--       (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (O x) x c L (pencil x\E) (f x) B T a) :
--       let q : ℝ := Nat.card K
--       let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
--       let t := zmin/(10*q)
--       let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
--       let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
--       Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
--           (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-Real.exp (-μmean/3)≤
--         (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω |
--           ((sample S ω).card:ℝ)≤2*μmean ∧
--           (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤
--             (S∩rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card ∧
--           ((rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card:ℝ)≤
--             2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin}
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.PoissonSchedules.scheduleLaw`, `OAI.SharpLogRamsey.PreparedRow.HighPencil`, `OAI.SharpLogRamsey.PreparedRow.SecondPencil`, `OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_3`, `OAI.SharpLogRamsey.PreparedRow.inc`, `OAI.SharpLogRamsey.PreparedRow.pencil` and `OAI.SharpLogRamsey.PreparedRow.sample` (definitions bundle `OAIQ045S001` of this split); `OAI.SharpLogRamsey.PreparedRow.rowTest` (definitions bundle `OAIQ045S002` of this split).
--
--   **Used by.** The proofs of `OAI.SharpLogRamsey.PlanarLearning.full_source_cover_uniform` and `OAI.SharpLogRamsey.SpatialPublic.actual_cover` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Learning/TestActualRow.lean (declaration OAI.SharpLogRamsey.PreparedRow.geometric_row_probability)

import Mathlib
import Definitions.Def_OAIQ045S002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory LearningRow
open scoped BigOperators Classical NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_2
attribute [local instance] OAI.SharpLogRamsey.PreparedRow.flat_JoinedTestActualRow_3
theorem geometric_row_probability
    (n R p h : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty) (hDa : Ds⊆Da)
    (O : Projectivization K V→Finset (Projectivization K V))
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (f : Projectivization K V→ℝ) (hf : ∀ x,f x≤1/25)
    (B C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-f x))*((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (O x) x c L (pencil x\E) (f x) B C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (O x) x c L (pencil x\E) (f x) B T a) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
        (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-Real.exp (-μmean/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω |
        ((sample S ω).card:ℝ)≤2*μmean ∧
        (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤
          (S∩rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card ∧
        ((rowTest S O E (fun x => Real.exp (-(L:ℝ)*(1-f x))) ω).card:ℝ)≤
          2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin} := by
  sorry

end
end SharpLogRamsey.PreparedRow

end

end OAI
end
