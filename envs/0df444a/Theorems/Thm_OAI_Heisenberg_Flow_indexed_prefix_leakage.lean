-- Prove2me | Theorems.Thm_OAI_Heisenberg_Flow_indexed_prefix_leakage
-- name    : OAI.Heisenberg.Flow.indexed_prefix_leakage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T08:28:05.810856+00:00
-- url     : https://prove2.me/theorems/df67a674-5070-4805-b9ba-c9e17a73069b
-- title:
--   OAI.Heisenberg.Flow.indexed_prefix_leakage: intermediate lemma from OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Heisenberg.spontaneous_magnetization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spontaneous magnetization in the quantum Heisenberg ferromagnet*, OpenAI Math Release, September 24, 2026, result family 271, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Heisenberg.Flow.indexed_prefix_leakage` of [lean/OAI/MathematicalPhysics/Heisenberg/PeriodicLeakage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/PeriodicLeakage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Heisenberg.Flow`, with `open scoped Classical BigOperators Fin.NatCast`, `open scoped Classical BigOperators Fin.NatCast RealInnerProductSpace`, `open Filter Topology`, `open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular`):
--
--   ```lean
--   theorem indexed_prefix_leakage (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
--       ∃ M : ℕ,∃ C ≥ 0,∀ (B : Type) [Fintype B] [Nonempty B]
--         (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
--         (edge : Fin q ≃ Edges (B:=B) Step Λ)
--         (a₀ b₀ : ℕ → Slots (B:=B) Λ)
--         (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
--         (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
--         (ε : ℝ),0 < ε →
--         ∀ᶠ δ in 𝓝 (0:ℝ),0 < δ → δ ≤ 2 →
--         ∀ (T : Type) [Fintype T] (m Q : ℕ) [NeZero m]
--           (s : Equiv.Perm T) (ι : Fin m ≃ T)
--           (_hι : ∀ j,s (ι j)=ι (finRotate m j))
--           (_hQ : 0 < Q) (_hqQ : q ≤ Q) (_hdiv : Q∣m)
--           (a b : T → Slots (B:=B) Λ)
--           (_hab : ∀ j : Fin m,∀ _hj : j.val%Q < q,
--             a (ι j)=a₀ (j.val%Q) ∧ b (ι j)=b₀ (j.val%Q))
--           (_hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
--           (p : T → ℝ) (_hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
--           (_hrate : ∀ j : Fin m,j.val%Q < q → p (ι j)=δ/2)
--           (P : Set (T×Slots (B:=B) Λ)) (t : Fin m)
--           (J : Finset (Slots (B:=B) Λ))
--           (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
--           (n R : ℕ) (ρ : ℝ),
--           0 < n → Heisenberg.Schedule.cut t Q n ≤ m →
--           F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
--           (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t) ∧ j.1.val∈F) →
--           (∀ base j,j∈J → (f base).ofLp j=1) →
--           (∀ base j,0 ≤ (f base).ofLp j ∧ (f base).ofLp j ≤ 1) →
--           (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩{j | j.1.val∈F} → (f base).ofLp j=0) →
--           (∀ z u,0 ≤ u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z ≤ u)).card:ℝ) ≤ L*(1+u)^((1:ℝ)/100)) →
--           (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b P p base *
--             (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base P (ι (run t (Heisenberg.Schedule.cut t Q i)))))
--               j.val.1.val R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
--           (J.card:ℝ)-2*((ρ+((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)*J.card)-
--             2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/((δ/2)*(n:ℝ))-
--             (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤
--           ∑ base,Exposure.layerMass s a b P p base *
--             (‖f base‖^2-‖exposedSweep s a b base P {v | v.1.val∈F} p (fun l=>ι (run t l)) (Heisenberg.Schedule.cut t Q n) (f base)‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Heisenberg.Exposure.exposedSweep`, `OAI.Heisenberg.Exposure.holeCut`, `OAI.Heisenberg.Exposure.layerMass`, `OAI.Heisenberg.Flow.periodicDecEq`, `OAI.Heisenberg.Geometry.Site`, `OAI.Heisenberg.Geometry.Step`, `OAI.Heisenberg.LatticeRegular.Regular`, `OAI.Heisenberg.Schedule.cut`, `OAI.Heisenberg.Schedule.run`, `OAI.Heisenberg.SpatialFrame.Edges`, `OAI.Heisenberg.SpatialFrame.Slots` and `OAI.Heisenberg.SpatialFrame.blocked` (definitions bundle `OAIW2HM000` of this split); `OAI.Heisenberg.Site` (the published bundle `Def_Heisenberg`).
--
--   **Used by.** The proof of `OAI.Heisenberg.Bootstrap.periodic_return_estimate` of this split imports it.
-- source:
--   OpenAI, Spontaneous magnetization in the quantum Heisenberg ferromagnet, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 271; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Spontaneous-magnetization-in-the-quantum-Heisenberg-ferromagnet-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/Heisenberg/PeriodicLeakage.lean (declaration OAI.Heisenberg.Flow.indexed_prefix_leakage)

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Classical BigOperators Fin.NatCast

noncomputable section
open scoped Classical BigOperators Fin.NatCast RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular
variable {d : ℕ}

attribute [local instance] OAI.Heisenberg.Flow.periodicDecEq
theorem indexed_prefix_leakage (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ,∃ C ≥ 0,∀ (B : Type) [Fintype B] [Nonempty B]
      (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
      (edge : Fin q ≃ Edges (B:=B) Step Λ)
      (a₀ b₀ : ℕ → Slots (B:=B) Λ)
      (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
      (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
      (ε : ℝ),0 < ε →
      ∀ᶠ δ in 𝓝 (0:ℝ),0 < δ → δ ≤ 2 →
      ∀ (T : Type) [Fintype T] (m Q : ℕ) [NeZero m]
        (s : Equiv.Perm T) (ι : Fin m ≃ T)
        (_hι : ∀ j,s (ι j)=ι (finRotate m j))
        (_hQ : 0 < Q) (_hqQ : q ≤ Q) (_hdiv : Q∣m)
        (a b : T → Slots (B:=B) Λ)
        (_hab : ∀ j : Fin m,∀ _hj : j.val%Q < q,
          a (ι j)=a₀ (j.val%Q) ∧ b (ι j)=b₀ (j.val%Q))
        (_hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
        (p : T → ℝ) (_hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
        (_hrate : ∀ j : Fin m,j.val%Q < q → p (ι j)=δ/2)
        (P : Set (T×Slots (B:=B) Λ)) (t : Fin m)
        (J : Finset (Slots (B:=B) Λ))
        (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
        (n R : ℕ) (ρ : ℝ),
        0 < n → Heisenberg.Schedule.cut t Q n ≤ m →
        F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
        (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t) ∧ j.1.val∈F) →
        (∀ base j,j∈J → (f base).ofLp j=1) →
        (∀ base j,0 ≤ (f base).ofLp j ∧ (f base).ofLp j ≤ 1) →
        (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩{j | j.1.val∈F} → (f base).ofLp j=0) →
        (∀ z u,0 ≤ u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z ≤ u)).card:ℝ) ≤ L*(1+u)^((1:ℝ)/100)) →
        (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b P p base *
          (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base P (ι (run t (Heisenberg.Schedule.cut t Q i)))))
            j.val.1.val R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
        (J.card:ℝ)-2*((ρ+((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)*J.card)-
          2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/((δ/2)*(n:ℝ))-
          (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤
        ∑ base,Exposure.layerMass s a b P p base *
          (‖f base‖^2-‖exposedSweep s a b base P {v | v.1.val∈F} p (fun l=>ι (run t l)) (Heisenberg.Schedule.cut t Q n) (f base)‖^2) := by
  sorry

end Heisenberg.Flow

end
end

end

end OAI
end
