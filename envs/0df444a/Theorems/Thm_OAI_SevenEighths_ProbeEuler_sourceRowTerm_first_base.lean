-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_sourceRowTerm_first_base
-- name    : OAI.SevenEighths.ProbeEuler.sourceRowTerm_first_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:50.662297+00:00
-- url     : https://prove2.me/theorems/f7d28039-a579-4cca-841b-003ec956bce1
-- title:
--   Base bound for source row terms
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda` with residue characteristic $\ne2$; let $\eta,a,\rho,x,w,z\in\mathbb C$ with $|\eta|,|a|\le1$, $\rho^6=1$, $\operatorname{Re}x\ge51/100$, $\operatorname{Re}w\ge-1/100$, $\operatorname{Re}z\ge17/50$, $\operatorname{Re}x+\operatorname{Re}w\ge1$; and $j,e,l,k,m$ with $j<6$, $k\le1$, $(e,l)\in\{(0,2),(1,0),(0,1),(1,1)\}$. Then $\|\texttt{sourceRowTerm}\,p\dots\eta\,a\,\rho\,x\,w\,z\,j\,e\,l\,k\,m\|\le2$.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.sourceRowTerm_first_base` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsFirstTerms.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

set_option maxHeartbeats 1000000 in
include hc in
theorem sourceRowTerm_first_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (_hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1≤x.re+w.re) (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2 := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
