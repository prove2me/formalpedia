-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_sourceRowTerm_central_nonstrict
-- name    : OAI.SevenEighths.ProbeEuler.sourceRowTerm_central_nonstrict
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:36.007982+00:00
-- url     : https://prove2.me/theorems/1cf15971-a4de-4852-90a6-53a1ef5c64c9
-- title:
--   Central bound for source row terms
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda` with residue characteristic $\ne2$, $N=N((p))$; let $\eta,a,\rho,x,w,z\in\mathbb C$ and reals $\alpha,\epsilon$ with $|\eta|,|a|\le1$, $\rho^6=1$, $51/100\le\alpha\le1$, $0<\epsilon\le1/1000$, $\operatorname{Re}x=\alpha+16\epsilon$, $\operatorname{Re}w=1-\alpha-6\epsilon$, $\operatorname{Re}z=17/50$; and $j,e,l,k,m\in\mathbb N$ with $j<6$, $k\le1$, $(e,l)\in\{(0,2),(1,0),(0,1),(1,1)\}$ and not ($e=1$, $l=0$, $k=1$, $m=0$). Then $\|\texttt{sourceRowTerm}\,p\dots\eta\,a\,\rho\,x\,w\,z\,j\,e\,l\,k\,m\|\le2N^{1/2-\operatorname{Re}x}$.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.sourceRowTerm_central_nonstrict` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsCentralTerms.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
