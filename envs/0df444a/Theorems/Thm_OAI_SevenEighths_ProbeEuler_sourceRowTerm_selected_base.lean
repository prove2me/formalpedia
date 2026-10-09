-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_sourceRowTerm_selected_base
-- name    : OAI.SevenEighths.ProbeEuler.sourceRowTerm_selected_base
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:44.419989+00:00
-- url     : https://prove2.me/theorems/4b5648de-c933-45a9-a3a8-bebdec5e02e9
-- title:
--   Selected bound for source row terms when Re x >= 7/8
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda` with residue characteristic $\ne2$, $N=N((p))$; let $\eta,a,\rho,x,w,z\in\mathbb C$ with $|\eta|,|a|\le1$, $\rho^6=1$, $\operatorname{Re}x\ge7/8$, $\operatorname{Re}w\ge1/2$, $\operatorname{Re}z\ge17/50$; and $j,e,l,k,m$ with $j<6$, $k\le1$, $(e,l)\in\{(0,2),(1,0),(0,1),(1,1)\}$. Then $\|\texttt{sourceRowTerm}\,p\dots\eta\,a\,\rho\,x\,w\,z\,j\,e\,l\,k\,m\|\le2N^{-\operatorname{Re}x+\max(1-\operatorname{Re}w,0)}$.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.sourceRowTerm_selected_base` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsSelectedTerms.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
theorem sourceRowTerm_selected_base (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (7/8:ℝ)≤x.re) (_hw : (1/2:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re+max (1-w.re) 0) := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
