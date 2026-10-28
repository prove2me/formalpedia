-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_ProjectiveIncidence_orientedGuardedNode_original
-- name    : OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:04:32.377789+00:00
-- url     : https://prove2.me/theorems/561965d2-b874-4aed-ab4b-5db236e6e880
-- title:
--   OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original` of [lean/OAI/Combinatorics/RamseyFive/Geometry/GuardedNode.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/GuardedNode.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.ProjectiveIncidence`, with `open Module FiniteEntropy ReverseCap ScoreGeometry`, `open scoped Classical LinearAlgebra.Projectivization`):
--
--   ```lean
--   theorem orientedGuardedNode_original
--       (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
--       (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
--       (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
--       (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
--       (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
--       (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) :
--       let p := map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
--         (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
--           (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))
--       (∀b,eventMass p (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
--           (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
--       (∀a,eventMass p (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
--           (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.eventMass`, `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.ScoreGeometry.FinitePredictor` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.ReverseCap.Excludes` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeMessage`, `OAI.SharpRamseyFive.ProjectiveIncidence.OrientedNodeTape`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeDecoded`, `OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeFintype` and `OAI.SharpRamseyFive.ProjectiveIncidence.orientedNodeTapeLaw` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNodeEncoded` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proofs of `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_target_retention` and `OAI.SharpRamseyFive.ProjectiveIncidence.eventually_ordered_tree_missing` of this split import it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Geometry/GuardedNode.lean (declaration OAI.SharpRamseyFive.ProjectiveIncidence.orientedGuardedNode_original)

import Mathlib
import Definitions.Def_OAIQ060R004

section

attribute [-instance] _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeMessageFintype _root_.OAI.SharpRamseyFive.ProjectiveIncidence.orientedPivotTreeTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

theorem orientedGuardedNode_original
    (f : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (r : FinitePredictor (ℙ K (Dual K V)) (ℙ K (Dual K (Dual K V))))
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hd : finrank K V=5) (hq3 : 3≤Nat.card K)
    (A₀ UA : Finset (ℙ K V)) (B₀ UB : Finset (ℙ K (Dual K V)))
    (hA₀ : A₀.Nonempty) (hB₀ : B₀.Nonempty) (c δ τ P : ℝ)
    (hc : 0 < c) (hc9 : c≤9/10) (hδ : 0<δ) (hτ : 1000*τ ≤ c*δ^2) :
    let p := map (orientedNodeTapeLaw f r (1000*(Nat.card K)^2) (Nat.card K)) (fun t=>
      (orientedGuardedNodeEncoded f r σ hσ hq hd.le A₀ UA B₀ UB hA₀ hB₀ c δ τ P hδ t).map
        (orientedNodeDecoded f r UA UB (1000*(Nat.card K)^2) (Nat.card K) t))
    (∀b,eventMass p (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass p (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  sorry

end SharpRamseyFive.ProjectiveIncidence

end OAI
end
