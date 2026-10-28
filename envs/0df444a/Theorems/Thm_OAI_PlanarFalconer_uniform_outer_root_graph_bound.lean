-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_uniform_outer_root_graph_bound
-- name    : OAI.PlanarFalconer.uniform_outer_root_graph_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:58:15.8346+00:00
-- url     : https://prove2.me/theorems/951833bb-5721-4cda-a4d0-bbcf92e212d7
-- title:
--   OAI.PlanarFalconer.uniform_outer_root_graph_bound: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.uniform_outer_root_graph_bound` of [lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/OuterRootGraphBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/OuterRootGraphBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer`, with `open Set MeasureTheory`, `open scoped ContDiff ENNReal`):
--
--   ```lean
--   theorem uniform_outer_root_graph_bound {lam sig kap eta T : ℝ}
--       (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
--       (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1)
--       (heta : 0 < eta) (hT : 0 ≤ T) (n : ℕ)
--       {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
--       (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
--       (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
--       ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
--         ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
--         (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
--         100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
--         ∀ B : ℕ, ∀ δ : ℝ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
--         ∀ c : ℕ, c+100*sourcePolicyBlock N kap < N → kap*N ≤ (c:ℝ) → 2*c ≤ N →
--         let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
--         let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
--           N lam lam sig kap c (Q 0) (Q 1)
--         let bound := ((2:ℝ)^N)^(min (height (A 0) 0 c) (height (A 1) 0 c)-
--           (potential (A 0) c N (10*sourcePolicyBlock N kap)+
--            potential (A 1) c N (10*sourcePolicyBlock N kap))/2+
--           500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+eta)+((2:ℝ)^N)^(-T)
--         (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
--           d.inversePhasedHF N Ψ b.2 ξ ≠ ⊤ ∧ (d.inversePhasedHF N Ψ b.2 ξ).toReal ≤ bound) ∧
--         d.inverseShellSupremum n N Ψ ≤ bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PolicyDescriptor`, `OAI.PlanarFalconer.RegularizedProfileData`, `OAI.PlanarFalconer.RootMaskIndex`, `OAI.PlanarFalconer.RootShellData`, `OAI.PlanarFalconer.height`, `OAI.PlanarFalconer.inverseLeibnizTerms`, `OAI.PlanarFalconer.potential`, `OAI.PlanarFalconer.sourcePolicyBlock`, `OAI.PlanarFalconer.DyadicSquare.carrier`, `OAI.PlanarFalconer.DyadicSquare.center`, `OAI.PlanarFalconer.RootShellData.indices`, `OAI.PlanarFalconer.RootShellData.inversePhasedHF`, `OAI.PlanarFalconer.RootShellData.inverseShellSupremum` and `OAI.PlanarFalconer.RootShellData.ofOuter` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.uniform_independent_class_equation27` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Graphs/OuterRootGraphBound.lean (declaration OAI.PlanarFalconer.uniform_outer_root_graph_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_outer_root_graph_bound {lam sig kap eta T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (hkap1 : kap ≤ 1)
    (hgap : sig < kap/1000) (hloss : 4000*(lam+sig) ≤ 1)
    (heta : 0 < eta) (hT : 0 ≤ T) (n : ℕ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : ℕ, ∀ δ : ℝ, (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
      ∀ c : ℕ, c+100*sourcePolicyBlock N kap < N → kap*N ≤ (c:ℝ) → 2*c ≤ N →
      let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      let bound := ((2:ℝ)^N)^(min (height (A 0) 0 c) (height (A 1) 0 c)-
        (potential (A 0) c N (10*sourcePolicyBlock N kap)+
         potential (A 1) c N (10*sourcePolicyBlock N kap))/2+
        500*kap+10^6*(lam+sig)/kap+4000*(lam+sig)+eta)+((2:ℝ)^N)^(-T)
      (∀ j ∈ Finset.range (n+1), ∀ b ∈ inverseLeibnizTerms j d.indices, ∀ ξ,
        d.inversePhasedHF N Ψ b.2 ξ ≠ ⊤ ∧ (d.inversePhasedHF N Ψ b.2 ξ).toReal ≤ bound) ∧
      d.inverseShellSupremum n N Ψ ≤ bound := by
  sorry

end PlanarFalconer

end OAI
end
