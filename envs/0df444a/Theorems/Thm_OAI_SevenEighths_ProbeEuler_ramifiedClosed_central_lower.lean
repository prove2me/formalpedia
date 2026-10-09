-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_ramifiedClosed_central_lower
-- name    : OAI.SevenEighths.ProbeEuler.ramifiedClosed_central_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:50:20.217878+00:00
-- url     : https://prove2.me/theorems/e537f26c-f2bf-401e-8701-70015dd0fc7a
-- title:
--   Lower bound for the ramified closed Euler factor
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, with $N=N((p))\ge4$; let $\eta,a,\rho,x,w,z\in\mathbb C$ and reals $\alpha,\epsilon$ with $198N^{-10\epsilon}\le1/2$, $|\eta|,|a|\le1$, $\rho^6=1$, $51/100\le\alpha\le1$, $0<\epsilon\le1/1000$, $\operatorname{Re}x=\alpha+16\epsilon$, $\operatorname{Re}w=1-\alpha-6\epsilon$, $\operatorname{Re}z=17/50$, and $j<6$. Then $\|\texttt{ramifiedClosed}\,p\dots\eta\,a\,\rho\,x\,w\,z\,j\|\ge1/2$.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.ramifiedClosed_central_lower` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsCentralLower.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B018

section

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedClosed_central_lower (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1) (heps : 0<eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    1/2≤‖ramifiedClosed p hp hg eta a rho x w z j‖ := by
  sorry
end SevenEighths.ProbeEuler
end

end OAI
end
