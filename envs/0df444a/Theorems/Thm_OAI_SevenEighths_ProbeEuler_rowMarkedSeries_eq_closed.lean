-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeEuler_rowMarkedSeries_eq_closed
-- name    : OAI.SevenEighths.ProbeEuler.rowMarkedSeries_eq_closed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:48:13.701554+00:00
-- url     : https://prove2.me/theorems/c21c5ddf-5bad-4258-a024-5c605a2ec97d
-- title:
--   The row-marked Euler series equals its closed form
-- statement:
--   Let $p$ be a prime Eisenstein integer generating a maximal ideal not containing `goodLambda`, $N=N((p))$, and $\eta,a,X,W,V,\rho\in\mathbb C$ with $\rho^6=1$, $|V|<1$ and $|$`evenRatio N a X V`$|<1$. For every $j<6$, `rowMarkedSeries p hp hg η a X W V ρ j` $=$ `rowClosedMarked p hp hg η a X W V ρ j`.
--
--   Lean: `OAI.SevenEighths.ProbeEuler.rowMarkedSeries_eq_closed` in `lean/OAI/NumberTheory/DirichletL/Detector/HighRowsClosed.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
theorem rowMarkedSeries_eq_closed (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=rowClosedMarked p hp hg eta a X W V rho j := by
  sorry

end SevenEighths.ProbeEuler
end

end OAI
end
