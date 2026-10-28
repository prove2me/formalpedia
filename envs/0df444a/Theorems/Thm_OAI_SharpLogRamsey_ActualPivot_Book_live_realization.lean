-- Prove2me | Theorems.Thm_OAI_SharpLogRamsey_ActualPivot_Book_live_realization
-- name    : OAI.SharpLogRamsey.ActualPivot.Book.live_realization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:23:14.521984+00:00
-- url     : https://prove2.me/theorems/baeadfdf-e4b1-42c6-a01e-06f92c3933d9
-- title:
--   OAI.SharpLogRamsey.ActualPivot.Book.live_realization: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpLogRamsey.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpLogRamsey.ActualPivot.Book.live_realization` of [lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Selection/LiveRealization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Selection/LiveRealization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpLogRamsey.ActualPivot`, with `open Finset Real Selection Selection.AuxiliarySupport`, `open FreshExecution TreeDecoder BinaryTree ChronologicalTree`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem Book.live_realization
--       (q : Law Y₀) (S : Finset I) (fallback : I)
--       (p : I→Law (Projectivization K (Module.Dual K V)))
--       (r : I→Law (Projectivization K V))
--       (goodA : I→Finset (Projectivization K (Module.Dual K V)))
--       (goodB : I→Finset (Projectivization K V)) (MA MB κA κB : I→ℝ)
--       (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
--       (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
--       (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
--       (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
--         (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
--       (counts : I→ℕ)
--       (target : Y₀→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
--       (hR : ∀ y,q.mass y≠0→∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target y i j).2 (target y i j).1)
--       (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
--       (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
--       (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
--       (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
--       (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
--       (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
--         goodIncidence (q.map (fun y=>(target y i j).1)) (r k) (GA i j) (goodB k)≤εA)
--       (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
--         goodIncidence (p k) (q.map (fun y=>(target y i j).2)) (goodA k) (GB i j)≤εB)
--       (hbadA : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).1∈GA i j then (0:ℝ) else 1))≤δA)
--       (hbadB : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
--       ∃ e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q,
--         (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
--           ∑ ω,e.μ.mass ω*((∑ i∈S,(counts i:ℝ))-
--           (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
--             (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
--             (fun _=>chronoRead b) (fun i=>List.ofFn (target (e.source ω) i)) z
--             (liveTree S fallback) (univ,univ)).length))≤
--           (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpLogRamsey.ActualPivot.Banks`, `OAI.SharpLogRamsey.ActualPivot.Book`, `OAI.SharpLogRamsey.ActualPivot.Code`, `OAI.SharpLogRamsey.ActualPivot.Realization`, `OAI.SharpLogRamsey.ActualPivot.banksLaw`, `OAI.SharpLogRamsey.ActualPivot.chronoRead`, `OAI.SharpLogRamsey.ActualPivot.goodIncidence`, `OAI.SharpLogRamsey.ActualPivot.realDecEq`, `OAI.SharpLogRamsey.ActualPivot.realizationBanksFintype`, `OAI.SharpLogRamsey.ActualPivot.treeError`, `OAI.SharpLogRamsey.ChronologicalTree.liveTree`, `OAI.SharpLogRamsey.FreshExecution.fullOutput`, `OAI.SharpLogRamsey.Incidence.Incident`, `OAI.SharpLogRamsey.PublicTables.piLaw`, `OAI.SharpLogRamsey.Selection.AuxiliarySupport`, `OAI.SharpLogRamsey.Selection.Law`, `OAI.SharpLogRamsey.ActualPivot.Book.chronoChoose`, `OAI.SharpLogRamsey.PublicTables.Law` and `OAI.SharpLogRamsey.Selection.Law.map` (definitions bundle `OAIQ045S000` of this split).
--
--   **Used by.** The proofs of `OAI.SharpLogRamsey.Selection.Windows.integer_population_realization` and `OAI.SharpLogRamsey.Selection.Windows.open_population_realization` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SharpRamsey/SharpRamsey/Selection/LiveRealization.lean (declaration OAI.SharpLogRamsey.ActualPivot.Book.live_realization)

import Mathlib
import Definitions.Def_OAIQ045S000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SharpLogRamsey.ActualPivot
open Finset Real Selection Selection.AuxiliarySupport
open FreshExecution TreeDecoder BinaryTree ChronologicalTree
open scoped Classical BigOperators
noncomputable section
variable {K V I Y₀ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  [Fintype I] [LinearOrder I] [Fintype Y₀] {d : ℕ} {b τ P H : ℝ}

attribute [instance] Realization.inst

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.realDecEq
variable (hdim : Module.finrank K V=d+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (d+3))
  (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/40000)

include hb

attribute [local instance] OAI.SharpLogRamsey.ActualPivot.realizationBanksFintype
theorem Book.live_realization
    (q : Law Y₀) (S : Finset I) (fallback : I)
    (p : I→Law (Projectivization K (Module.Dual K V)))
    (r : I→Law (Projectivization K V))
    (goodA : I→Finset (Projectivization K (Module.Dual K V)))
    (goodB : I→Finset (Projectivization K V)) (MA MB κA κB : I→ℝ)
    (X : ∀ i : S,AuxiliarySupport (p i) (goodA i) (MA i) (κA i))
    (Y : ∀ i : S,AuxiliarySupport (r i) (goodB i) (MB i) (κB i))
    (hMA : ∀ i∈S,0<MA i) (hMB : ∀ i∈S,0<MB i)
    (hprod : ∀ i∈S,(Nat.card K:ℝ)^(d+3)*exp (-b)≤
      (MA i*exp (-κA i)/2)*(MB i*exp (-κB i)/2))
    (counts : I→ℕ)
    (target : Y₀→∀ i,Fin (counts i)→Projectivization K (Module.Dual K V)×Projectivization K V)
    (hR : ∀ y,q.mass y≠0→∀ i∈S,∀ j,SharpLogRamsey.Incidence.Incident (target y i j).2 (target y i j).1)
    (GA : ∀ i,Fin (counts i)→Finset (Projectivization K (Module.Dual K V)))
    (GB : ∀ i,Fin (counts i)→Finset (Projectivization K V))
    (ε εA εB δA δB : ℝ) (hε : 0≤ε) (hεA : 0≤εA) (hεB : 0≤εB)
    (hfirst : ∀ i∈S,∀ j∈S,i < j → goodIncidence (p i) (r j) (goodA i) (goodB j)≤ε)
    (hself : ∀ i∈S,goodIncidence (p i) (r i) (goodA i) (goodB i)≤ε)
    (hmeanA : ∀ i∈S,∀ j,∀ k∈S,i ≤ k →
      goodIncidence (q.map (fun y=>(target y i j).1)) (r k) (GA i j) (goodB k)≤εA)
    (hmeanB : ∀ i∈S,∀ j,∀ k∈S,k ≤ i →
      goodIncidence (p k) (q.map (fun y=>(target y i j).2)) (goodA k) (GB i j)≤εB)
    (hbadA : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).1∈GA i j then (0:ℝ) else 1))≤δA)
    (hbadB : ∀ i∈S,∀ j,(∑ y,q.mass y*(if (target y i j).2∈GB i j then (0:ℝ) else 1))≤δB) :
    ∃ e : Realization (K:=K) (V:=V) (I:=I) (d:=d) (b:=b) q,
      (∑ z,(PublicTables.piLaw (fun _ : I=>banksLaw (K:=K) (V:=V) b)).mass z*
        ∑ ω,e.μ.mass ω*((∑ i∈S,(counts i:ℝ))-
        (fullOutput (fun y x=>SharpLogRamsey.Incidence.Incident x y)
          (fun i=>book.chronoChoose hdim hτ.le hτsmall (e.supports ω i))
          (fun _=>chronoRead b) (fun i=>List.ofFn (target (e.source ω) i)) z
          (liveTree S fallback) (univ,univ)).length))≤
        (∑ i∈S,(counts i:ℝ))*treeError (Nat.card K) τ (liveTree S fallback).height ε εA εB δA δB := by
  sorry
end
end SharpLogRamsey.ActualPivot

end

end OAI
end
