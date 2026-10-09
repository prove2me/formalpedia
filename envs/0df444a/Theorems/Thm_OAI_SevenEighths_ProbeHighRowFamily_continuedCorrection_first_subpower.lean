-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_continuedCorrection_first_subpower
-- name    : OAI.SevenEighths.ProbeHighRowFamily.continuedCorrection_first_subpower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:46.989809+00:00
-- url     : https://prove2.me/theorems/8c8fbb83-e44c-4159-83ef-ce39169a5c09
-- title:
--   Subpower bound for the continued correction
-- statement:
--   For every $\varepsilon>0$ there is $C>0$ such that for every $\epsilon$, every $S$ with `SourceExclusions S` and `FirstTail ε S`, every `Character` $\eta$, `FreeRow` $u$ and $x,w,z$ with $\operatorname{Re}x\ge51/100$, $\operatorname{Re}w\ge-1/100$, $\operatorname{Re}z\ge17/50$, $\operatorname{Re}x+\operatorname{Re}w\ge1+\epsilon$: $\|\texttt{continuedCorrection}\,S\,hS\,\eta\,u\,x\,w\,z\|\le C\,N((u))^{\varepsilon}$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.continuedCorrection_first_subpower` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/FirstContinuation.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

theorem continuedCorrection_first_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (_hfirst : FirstTail eps S) (η : Character) (u : FreeRow) (x w z : ℂ),
      (51/100:ℝ)≤x.re → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      1+eps≤x.re+w.re →
      ‖continuedCorrection S hS η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm : ℝ)^ε := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
