-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_reference_density_le_bs
-- name    : OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:20:25.809167+00:00
-- url     : https://prove2.me/theorems/e7c19104-ecea-475c-8c5d-cbdc6d563d96
-- title:
--   OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le` of [lean/OAI/Probability/CriticalPercolation/Entropy/BinaryReferenceLikelihood.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryReferenceLikelihood.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BinaryLaw`, with `open scoped Classical`, `open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree`):
--
--   ```lean
--   lemma conditioned_reference_density_le_bs (s : ℕ) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
--       (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
--       {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
--       (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
--       (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
--       (hD : 0 < descriptorMass G order d x p w s n D)
--       (z : (E → Bool) × (Fin n → Option E)) :
--       conditionedMass G order d x p w s n D z ≤
--         inverseReference G order d x p w n D (recorded n D z) *
--         Real.exp (constructionCost G order d x p w c s n D + inverseLog G order d x p w n D z.1 z.2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BinaryLaw.FixedDescriptor`, `OAI.CriticalPercolation.BinaryLaw.conditionedMass`, `OAI.CriticalPercolation.BinaryLaw.constructionCost`, `OAI.CriticalPercolation.BinaryLaw.descriptorMass`, `OAI.CriticalPercolation.BinaryLaw.endpointEvent`, `OAI.CriticalPercolation.BinaryLaw.inverseLog`, `OAI.CriticalPercolation.BinaryLaw.inverseReference`, `OAI.CriticalPercolation.BinaryLaw.recorded`, `OAI.CriticalPercolation.BondGraph.openGraph`, `OAI.CriticalPercolation.FiniteProduct.prob` and `OAI.CriticalPercolation.LazyDFS.Dart` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryReferenceLikelihood.lean (declaration OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]

variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

lemma conditioned_reference_density_le_bs (s : ℕ) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      inverseReference G order d x p w n D (recorded n D z) *
      Real.exp (constructionCost G order d x p w c s n D + inverseLog G order d x p w n D z.1 z.2) := by
  sorry

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end
