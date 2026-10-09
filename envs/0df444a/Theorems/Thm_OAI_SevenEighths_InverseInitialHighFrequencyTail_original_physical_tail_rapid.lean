-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialHighFrequencyTail_original_physical_tail_rapid
-- name    : OAI.SevenEighths.InverseInitialHighFrequencyTail.original_physical_tail_rapid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:53:29.57026+00:00
-- url     : https://prove2.me/theorems/2ff8f883-3189-4c2d-884a-f21b47feac23
-- title:
--   Rapid decay of the original physical tail at high frequency
-- statement:
--   For reals $L_{\mathrm{cap}}$, `saving` and $\tau>0$ there are a finite $s\subseteq\mathbb N\times\mathbb N$ and $C_0>0$ such that: for every family $p:\iota\to\mathcal O$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` with residue characteristic $\ne2$, every multiplicative $\Psi$ bounded by 1, $j\in\mathcal O$, slot data with pairwise disjoint `lists` and coefficients bounded by 1, $W_1,W_2$ bounded by $B_1,B_2\ge0$, a Schwartz $\Phi$, reals $Z\ge1$, $1\le L\le Z^{L_{\mathrm{cap}}}$, $0\le L_{\mathrm{cap}}$, $-m\le L_{\mathrm{cap}}$, $m-D\le L_{\mathrm{cap}}$, $\Gamma\ge0$, a finite `pool`, a finite set $S$ of `Valid` points with weights bounded by $\Gamma$, source keys inside `pool` with `primeProductNorm` at most $L$, the common·overlap·left and common·overlap·right products at most $L$, and $Z^\tau\le Z^m\|\texttt{eisEmbedding}(x.\mathrm{frequency})\|^2/(\text{divisor}\cdot\text{overlap}^2\cdot\text{left}\cdot\text{right norms})$ for each $x\in S$:
--   $$\|\texttt{physicalBlock}\ p\ \dots\ S\,w\,\Psi\,j\,(\texttt{primeMark}\dots)\,W_1\,W_2\,\Phi\,Z\,D\,m\|\le C_0\,\Gamma\,B_1B_2\,\sup_s(\text{seminorms of }\Phi)\,Z^{-\mathrm{saving}}.$$
--
--   Lean: `OAI.SevenEighths.InverseInitialHighFrequencyTail.original_physical_tail_rapid` in `lean/OAI/NumberTheory/DirichletL/Inversion/InitialHighFrequencyTailRapid.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B012

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
local notation "O"=>ActualEisensteinCubic.O

theorem original_physical_tail_rapid (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C₀ : ℝ), 0<C₀ ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m L Γ B₁ B₂ : ℝ),
    1≤Z → 1≤L → 0≤Lcap → L≤Z^Lcap → -m≤Lcap → m-D≤Lcap → 0≤Γ → 0≤B₁ → 0≤B₂ →
    (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    ∀ (pool : Finset ι) (S : Finset (Point ι)) (w : Point ι→ℂ),
    (∀x∈S,Valid x) → (∀x∈S,‖w x‖≤Γ) →
    (∀x∈S,∀i,sourceKey x i⊆pool) →
    (∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤L) →
    (∀x∈S,primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤L) →
    (∀x∈S,Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2) →
    ‖physicalBlock p hp hcop hg S w Ψ j (primeMark slots lists a) W₁ W₂ Φ Z D m‖ ≤
      C₀*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  sorry

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
end
