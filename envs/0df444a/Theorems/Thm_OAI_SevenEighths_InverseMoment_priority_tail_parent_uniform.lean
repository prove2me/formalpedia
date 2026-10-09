-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_priority_tail_parent_uniform
-- name    : OAI.SevenEighths.InverseMoment.priority_tail_parent_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:38.357451+00:00
-- url     : https://prove2.me/theorems/512f91dc-7feb-4008-bc30-c1192bfb346a
-- title:
--   Rapid decay of priority tail parents
-- statement:
--   For reals $L_{\mathrm{cap}}\ge0$, $\tau>0$ and `saving` there are a finite $s\subseteq\mathbb N\times\mathbb N$ and $C>0$ such that for every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` with residue characteristic $\ne2$, every `extra`, `pool`, Boolean `negative`, $\Psi$ bounded by 1, $m$, slots and an assigned subset with pairwise disjoint lists and coefficients bounded by 1, every Schwartz $\omega$ supported in $[lo,hi]$ ($lo>0$), reals $X>0$, $M$ with $hi\le e^M$, $Z\ge1$, $Y>0$, $t$, with $1\le Xe^M\le Z^{L_{\mathrm{cap}}}$, $Y\le Z^{L_{\mathrm{cap}}}$, $Y^{-1}\le Z^{L_{\mathrm{cap}}}$, a cutoff $R$, and every `SecondParentSource` $y$ whose `correlatedSecondRadius` at every $G\subseteq$ `pool`, $E\subseteq G$ is at most $R(G,E)$:
--   $$\|\texttt{priorityTailParent}(\dots,\texttt{principalWindow}\,\omega\dots t,X,Y,R,y)\|\le C\,\|\texttt{rowMajorant}\|_s\,\|\omega\|_{0,0}^2\,Z^{-\mathrm{saving}}.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.priority_tail_parent_uniform` in `lean/OAI/NumberTheory/DirichletL/Descent/WholePriorityParentBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O

variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

theorem priority_tail_parent_uniform (Lcap tau saving:ℝ)(hLcap:0≤Lcap)(htau:0<tau):
    ∃(s:Finset (ℕ×ℕ))(C:ℝ),0<C ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) → (∀u,‖Ψ u‖≤1) →
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (X M Y Z t:ℝ)(R:Finset ι→Finset ι→ℝ),
      0<X → hi≤Real.exp M → 1≤Z → 0<Y → 1≤X*Real.exp M →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → X*Real.exp M≤Z^Lcap →
    ∀{Jo:ℕ}(y:SecondParentSource ι Jo),
      (∀G∈pool.powerset,∀E:G.powerset,
        correlatedSecondRadius p (secondParentDivisor p y) G E.val (X*Real.exp M) Y (Z^tau)≤R G E.val) →
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ m slots assigned lists a
        (principalWindow om lo hi hlo hs negative t) X Y R y‖≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*(SchwartzMap.seminorm ℝ 0 0 om)^2*Z^(-saving):= by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
