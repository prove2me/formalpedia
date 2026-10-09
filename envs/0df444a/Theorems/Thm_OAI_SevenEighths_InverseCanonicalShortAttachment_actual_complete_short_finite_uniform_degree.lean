-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseCanonicalShortAttachment_actual_complete_short_finite_uniform_degree
-- name    : OAI.SevenEighths.InverseCanonicalShortAttachment.actual_complete_short_finite_uniform_degree
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:59.792363+00:00
-- url     : https://prove2.me/theorems/fffabe76-fa62-4676-8388-96735e2525bc
-- title:
--   Saving for complete short sums with marked prime slots
-- statement:
--   Let $W$ be smooth with support in $[lo,hi]$, $lo>0$, reals $L\ge0$, $c^*>0$, $0<\eta\le\min(1,c^*/100000)$, and $r_{\max},K\in\mathbb N$. Then there is a degree such that for every $q\ne0$ there are $C>0$, $Z_0>1$ such that for every slot type $\sigma$, $m\ne0$ with $N((m))\le Z^L$, reals $Z\ge Z_0$, $N,V,M\ge0$ with $M,V,z_0\le L$, $0\le h_{\mathrm{cut}}\le L$, `CanonicalMargins (N+V) M (normWidth Z (m)) z₀ margin` with margin $\ge c^*/2$, $V\le d$, $h_{\mathrm{cut}}\le d+\eta$, $d\le c^*/200$; `labels` of `Supported` squarefree ideals of norm $\le Z^V$; a finite set $T$ of nonzero elements with $N((k))\le Z^M$; $D\ge hi\,Z^N$; at most $r_{\max}$ slots with pairwise disjoint lists of primes of norm $\le H_j$ ($H_j\ge1$, $\prod H_j\le Z^{z_0}$) and coefficients bounded by 1; $\Psi$ bounded by 1 factoring modulo `fixedBaseConductor q`; and $\theta$: with $S=$`reflectionExcludedPrimes q` and the slot mark,
--   $$Z^{-V}\sum_{f\in\mathrm{labels}}\texttt{secondLabelWeight}\,K\,f\sum_{k\in T}\|\texttt{markedShortCompletedSum}(\texttt{rowTwist}\,\Psi\,(m\cdot\texttt{excludedGenerator}\,S)\,f_{\mathrm{gen}}\,k,\ \texttt{normTwistedSource}\,W\,\theta,\ Z^N,\ Z^{h_{\mathrm{cut}}},\ \mathrm{mark})\|^2\le C(1+|\theta|)^{\mathrm{degree}}Z^{N+V-c^*/256}.$$
--
--   Lean: `OAI.SevenEighths.InverseCanonicalShortAttachment.actual_complete_short_finite_uniform_degree` in `lean/OAI/NumberTheory/DirichletL/Descent/CanonicalShortFinite.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped BigOperators Classical ContDiff
namespace SevenEighths.InverseCanonicalShortAttachment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve InverseMoment InverseReflectedPhase InverseTerminalWidths CompletedHeight
local notation "Eis"=>ActualEisensteinCubic.O
universe u v
theorem actual_complete_short_finite_uniform_degree
    (lo hi : ℝ) (hlo : 0<lo) (W : ℝ→ℂ)
    (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar eta : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (heta : 0<eta)
    (heta1 : eta≤1) (hetac : eta≤ cstar/100000) (rmax K : ℕ) :
    ∃ (degree : ℕ), ∀ (q:ℕ)(_hq:q≠0), ∃ (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [DecidableEq σ],
    ∀ (m : Eis),m≠0 → ∀ (Z N V M z₀ margin hcut d : ℝ),
      Z₀≤Z → 0≤N → 0≤V → 0≤M → M≤L → V≤L → z₀≤L → 0≤hcut → hcut≤L →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      V≤d → hcut≤d+eta → d≤ cstar/200 →
    ∀ (labels : Finset (Ideal Eis)),
      (∀f∈labels,Supported f ∧ Squarefree f ∧ (Ideal.absNorm f:ℝ)≤Z^V) →
    ∀ (T : Finset Eis),(∀k∈T,k≠0 ∧ (Ideal.absNorm (Ideal.span {k}):ℝ)≤Z^M) →
    ∀ D : ℕ,hi*Z^N≤D → ∀ slots : Finset σ,slots.card≤ rmax →
    ∀ (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
      (H : σ→ℝ),
      (slots:Set σ).Pairwise (fun j k=>Disjoint (lists j) (lists k)) →
      (∀j∈slots,1≤H j) → (∀j∈slots,∀i∈lists j,(Ideal.absNorm i.val:ℝ)≤H j) →
      (∏j∈slots,H j)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀n,‖Ψ n‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (θ : ℝ)
      (a : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ),
      (∀j∈slots,∀i∈lists j,‖a j i‖≤1) →
      let S:=reflectionExcludedPrimes q
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
      let mark:=indexedIdealMark (fun i:primePool F=>i.val) slots lists a
      Z^(-V)*(∑f∈labels,secondLabelWeight K f*∑k∈T,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator f) k)
          (normTwistedSource W θ) (Z^N) (Z^hcut) mark‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/256) := by
  sorry

end SevenEighths.InverseCanonicalShortAttachment

end

end OAI
end
