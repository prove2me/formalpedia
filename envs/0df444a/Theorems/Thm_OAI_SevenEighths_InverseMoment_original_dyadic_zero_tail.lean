-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_dyadic_zero_tail
-- name    : OAI.SevenEighths.InverseMoment.original_dyadic_zero_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:15:32.291985+00:00
-- url     : https://prove2.me/theorems/36776a0b-c73b-4ca1-a796-7b43236d1cbe
-- title:
--   Zero-mode and tail parts of the original dyadic family
-- statement:
--   Let $\omega$ be Schwartz vanishing beyond $b$, and $M_{\max},F_{\max},\eta\ge0$, $\tau>0$, `saving`, $\varepsilon>0$. Then there are $C_{\mathrm{zero}},C_{\mathrm{tail}}\ge0$ such that for every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` with residue characteristic $\ne2$, `pool`, finite $Q$ with cube primary products $\le Z^{\ell+\eta}$, nonzero `labels` of norm $\le Z^{V+\eta}$, coefficients $\beta$ bounded by $\Gamma\ge0$, $\Psi$ bounded by 1, $m$, slots with pairwise disjoint lists and weights bounded by 1, and reals $Z>1$, $Z^\eta\ge2$, $0\le M\le M_{\max}$, $\ell,V\ge0$, $-\eta\le r$, $r+3\ell+V\le F_{\max}$, $b\le Z^\eta$, $\theta$: with $W(y)=$`normTwistedSource ω θ (y/Z^r)` and the marks `primeMark`, (1) $Z^{-r-2\ell-V}$ times the norm of the `reopenedPhysicalSourceSum` of `canonicalCubeDualZero` (at `rowMajorant`, $Z^M$) is at most $C_{\mathrm{zero}}\Gamma^2Z^{M-\ell+3\eta+\varepsilon(5\ell+2r+7\eta)}$; and (2) the norm of the `reopenedPhysicalSourceSum` of `canonicalCubeDualTail` (with `firstDyadicPhysicalCutoff`) is at most $C_{\mathrm{tail}}\Gamma^2Z^{-\mathrm{saving}}$.
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_dyadic_zero_tail` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstDyadicOriginalBranches.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight SecondPassIntegration FourierBridge
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤b)(hMm:0≤Mmax)(hFm:0≤Fmax)(heta:0≤eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤Z^eta→0≤M→M≤Mmax→0≤ell→0≤V→ (-eta≤ r) → (r+3*ell+V≤Fmax)→0≤Γ→b≤Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤Ctail*Γ^2*Z^(-saving):= by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
