-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_ramifiedStrictSelected_boundary_norm
-- name    : OAI.SevenEighths.ProbeEuler.ramifiedStrictSelected_boundary_norm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:54:30.064842+00:00
-- url     : https://prove2.me/theorems/efc06331-4677-4246-b82f-79ac05609284
-- title:
--   Boundary bound for the ramified strict selected factor
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, with $N=N((p))\ge4$; let $\eta,a,\rho,x,w,z\in\mathbb C$ with $|\eta|,|a|\le1$, $\rho^6=1$, $\operatorname{Re}x\ge51/100$, $\operatorname{Re}z\ge17/50$, and $j\le1$. Then $\|\texttt{ramifiedStrictSelected}\,p\dots\eta\,a\,\rho\,x\,w\,z\,j\|\le6N^{-\operatorname{Re}w}$.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.ramifiedStrictSelected_boundary_norm` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsCentralStrictSelected.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  sorry
end SevenEighths.ProbeEuler
end

end OAI
end
