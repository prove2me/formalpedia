-- Prove2me | Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseRawInputBound_raw_input_bound
-- name    : OAI.SevenEighths.DetectorDictionaryInverseRawInputBound.raw_input_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:14:51.816898+00:00
-- url     : https://prove2.me/theorems/5bc78b75-208d-4d5a-a58a-822d3fc48260
-- title:
--   Bound for the raw conjugate input rows
-- statement:
--   Let $W,\Phi$ be Schwartz with $W$ supported in $[a,b]$, $a>0$, and reals `gap`, $\varepsilon,\pi,\eta,\tau$, `loss` positive with $\eta\le1$, $\eta\le\mathrm{gap}/50$, $\tau\le\mathrm{gap}/50$. Then there are $J$ and $B_{\mathrm{tree}}\ge1$ such that for every $q\ne0$ there are $C>0$, $Z_0>1$ such that for all $Z\ge Z_0$ and $D_{\mathrm{pool}}\ge B_{\mathrm{tree}}Z^3$, with $F=$`outsideSquarefreeIdeals (reflectionExcludedPrimes q) D_pool` and its prime pool $p$, every multiplicative $\Psi$ bounded by 1 factoring modulo `fixedBaseConductor q`, and reals $r,t$ with $-2\le r\le1-2\,\mathrm{gap}$, $2r\le3-2\,\mathrm{gap}$, $r+7\eta\le2$:
--   $$\Big\|\sum_{u\in\mathcal O}\Phi(\|\texttt{eisEmbedding}\,u\|^2/Z)\,\big\|Z^{-r/2}\,\texttt{inputConjugateRow}\,p\dots\Psi\,1\,1\,1\,(\texttt{initialTest}\,p\,1\,(\texttt{childLogTest}\,W\,t)\,Z\,r)\,u\big\|^2\Big\|\le C\,Z^{1+15\eta+\pi+\varepsilon+\mathrm{loss}}(1+|t|)^{2J}.$$
--
--   Lean: `OAI.SevenEighths.DetectorDictionaryInverseRawInputBound.raw_input_bound` in `lean/OAI/NumberTheory/DirichletL/Dictionary/InverseRawInputBound.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawInputBound
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT CompletedGauss SecondPassArithmetic CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalCoefficientClass InverseMoment InverseInitialProfile InverseInitialRayAttachment
open InverseInitialQuotientGeometry InverseInitialProfileBounds
local notation "O"=>ActualEisensteinCubic.O

theorem raw_input_bound
    (W:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support W⊆Set.Icc a b)
    (Φ:𝓢(ℝ,ℂ))(gap eps π η τ loss:ℝ)
    (hgap:0<gap)(heps:0<eps)(hπ:0<π)(hη:0<η)(hηone:η≤1)
    (hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss):
    ∃J:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^3≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hg:=poolPrimary_good F hF;
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀ (r t : ℝ), (-2 : ℝ) ≤ r → r ≤ 1 - 2 * gap → 2 * r ≤ 3 - 2 * gap → r + 7 * η ≤ 2 →
    ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z)*
      (‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ 1 1 1
        (initialTest p (fun _=>1) (childLogTest W t) Z r) u‖^2:ℝ)‖≤
      C*Z^(1+15*η+π+eps+loss)*(1+‖t‖)^(2*J) := by
  sorry

end SevenEighths.DetectorDictionaryInverseRawInputBound

end

end OAI
end
