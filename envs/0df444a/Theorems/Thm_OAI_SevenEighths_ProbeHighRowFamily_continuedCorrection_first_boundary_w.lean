-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_continuedCorrection_first_boundary_w
-- name    : OAI.SevenEighths.ProbeHighRowFamily.continuedCorrection_first_boundary_w
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:47.590543+00:00
-- url     : https://prove2.me/theorems/15a87387-37d7-415b-9870-c535447e962b
-- title:
--   The continued correction is analytic in w on the first boundary
-- statement:
--   Let $\epsilon>0$, $S$ with `SourceExclusions S` and `FirstTail (ε/2) S`, $\eta$ a `Character`, $u$ a `FreeRow`, and $x,w,z$ with $\operatorname{Re}x\ge51/100$, $\operatorname{Re}w\ge-1/100$, $\operatorname{Re}z\ge17/50$, $\operatorname{Re}x+\operatorname{Re}w\ge1+\epsilon$. Then $w'\mapsto$`continuedCorrection S hS η u x w' z` is complex-analytic at $w$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.continuedCorrection_first_boundary_w` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/FirstBoundary.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem continuedCorrection_first_boundary_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    AnalyticAt ℂ (fun w=>continuedCorrection S hS η u x w z) w := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
