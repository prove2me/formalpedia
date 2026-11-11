-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_LightPoint_computed_candidates_progress
-- name    : OAI.CurrentKS.State.LightPoint.computed_candidates_progress
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:59.441292+00:00
-- url     : https://prove2.me/theorems/78e37248-8b70-4ebe-aad6-54321c6191b8
-- title:
--   OAI.CurrentKS.State.LightPoint.computed_candidates_progress: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State.LightPoint`, with `open Matrix`, `open CurrentKS.Difference CurrentKS.RationalRoot`, `open scoped ContDiff`):
--
--   ```lean
--   theorem computed_candidates_progress [NeZero d] [NeZero N]
--       (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (hpx : p.x=pointCast x)
--       (lam : ℝ) (h a M s ρ : ℚ) (ha : 0<a) (ha1 : a≤1) (hM1 : 1≤M)
--       (hrel : lam=512*(a:ℝ)*p.C1^2)
--       (hs : 0 < s) (hs1 : s≤1/4) (hstep : M*s≤a/4) (hh : 0<h) (hh1 : h≤1)
--       (hhsmall : h≤a/(64*M*N)) (hρ : 0<ρ) (hmesh : (N:ℚ)*ρ/2 ≤ s *(a/(1024*M))/8)
--       (hreg : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 (p.Psi lam) y)
--       (hders : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖≤1 →
--         |iteratedDeriv 2 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ) ∧
--         |iteratedDeriv 3 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ))
--       (hquery : ∀ y,‖pointCast y-pointCast x‖≤2*(h:ℝ) →
--         |(query y:ℝ)-p.Psi lam (pointCast y)|≤(a:ℝ)*(h:ℝ)^2/(128*N)) :
--       ∃ y∈interiorCandidates query x h a M s ρ,
--         p.Psi lam (pointCast y)≤p.Psi lam p.x-2*(a:ℝ)*(s:ℝ)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Difference.interiorCandidates` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Difference.pointCast`, `OAI.CurrentKS.State.Coordinates`, `OAI.CurrentKS.State.LightPoint`, `OAI.CurrentKS.State.LightPoint.C1` and `OAI.CurrentKS.State.LightPoint.Psi` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.RationalFace.faceCandidates_progress` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT000
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Difference CurrentKS.RationalRoot
open scoped ContDiff

variable {d N : ℕ} (p : LightPoint d N)

theorem computed_candidates_progress [NeZero d] [NeZero N]
    (query : (Fin N → ℚ) → ℚ) (x : Fin N → ℚ) (hpx : p.x=pointCast x)
    (lam : ℝ) (h a M s ρ : ℚ) (ha : 0<a) (ha1 : a≤1) (hM1 : 1≤M)
    (hrel : lam=512*(a:ℝ)*p.C1^2)
    (hs : 0 < s) (hs1 : s≤1/4) (hstep : M*s≤a/4) (hh : 0<h) (hh1 : h≤1)
    (hhsmall : h≤a/(64*M*N)) (hρ : 0<ρ) (hmesh : (N:ℚ)*ρ/2 ≤ s *(a/(1024*M))/8)
    (hreg : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ContDiffAt ℝ 3 (p.Psi lam) y)
    (hders : ∀ y,‖y-pointCast x‖≤(s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖≤1 →
      |iteratedDeriv 2 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => p.Psi lam (y+t • u)) 0|≤(M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖≤2*(h:ℝ) →
      |(query y:ℝ)-p.Psi lam (pointCast y)|≤(a:ℝ)*(h:ℝ)^2/(128*N)) :
    ∃ y∈interiorCandidates query x h a M s ρ,
      p.Psi lam (pointCast y)≤p.Psi lam p.x-2*(a:ℝ)*(s:ℝ)^2 := by
  sorry

end
end CurrentKS.State.LightPoint

end OAI
end
