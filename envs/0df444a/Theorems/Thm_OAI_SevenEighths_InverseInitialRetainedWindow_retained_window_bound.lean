-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialRetainedWindow_retained_window_bound
-- name    : OAI.SevenEighths.InverseInitialRetainedWindow.retained_window_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:13:44.098677+00:00
-- url     : https://prove2.me/theorems/1d4cbd84-b787-42f8-9537-8fd0f7741d8e
-- title:
--   Physical block bound for windowed retained sources
-- statement:
--   Let $W_1,W_2$ be smooth with support in $[a_0,b_0]$, $a_0>0$, $b_{\mathrm{cap}}\ge1$, $\Phi$ Schwartz, $lo,hi:\mathrm{Fin}\,4\to\mathbb R$ with $0<lo_i\le hi_i$, reals $\mathrm{cap}\ge0$, `gap`, $\varepsilon$, $\pi$ positive, $U\ge0$, $K\in\mathbb N$. Then there are a degree, $B_{\mathrm{tree}}\ge1$ and $T_{\mathrm{clip}}\ge0$ such that for every $q\ne0$ there are $C>0$, $Z_0>1$ such that for all $Z\ge Z_0$, $D_{\mathrm{pool}}\ge B_{\mathrm{tree}}Z^{\mathrm{cap}+1}$, slot data with assigned and unassigned slots as in the finite physical bound, $\Psi$ bounded by 1 factoring modulo `fixedBaseConductor q`, a finite set $S$ of `Source 0` points (divisor in common part, nonzero frequency), window functions $\psi_i$ supported in $[lo_i,hi_i]$, reals $D,B,v,\theta,H,m,r,\eta,\tau$ with $0\le\eta\le\mathrm{gap}/50$, $\tau\le\mathrm{gap}/50$, $hi_i\le Z^\eta$, $Z^{-\eta}\le lo_1$, $T_{\mathrm{clip}}\le3\eta\log Z$, the center constraints of the finite physical bound, $B-\theta+2\eta\le U$, `radialCenter m H θ D B` $\le4\eta+\tau$, $1\le c_1,c_2\le b_{\mathrm{cap}}$, $\theta_1,\theta_2$ and weights bounded by 1: the norm of `physicalBlock` over `windowSource p S ψ Z D B v θ H` (with `assignedElement`, the unassigned `primeMark` and the two `clippedSource`s) is at most $C\,Z^{m+15\eta+\pi+\varepsilon}(1+|\theta_1|)^k(1+|\theta_2|)^k$, $k=$`momentOrder (4·degree)`.
--
--   Lean: `OAI.SevenEighths.InverseInitialRetainedWindow.retained_window_bound` in `lean/OAI/NumberTheory/DirichletL/Inversion/InitialRetainedWindow.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.InverseInitialRetainedWindow
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialEnergyCallerSourceMask InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialCanonicalState FirstPassCubeLabels
local notation "O"=>ActualEisensteinCubic.O

theorem retained_window_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (lo hi:Fin 4→ℝ)(hlo:∀i,0<lo i)(hhi:∀i,lo i≤hi i)
    (cap gap eps U π:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hU:0≤U)(hπ:0<π)(K:ℕ):
    ∃degree:ℕ,∃Btree Tclip:ℝ,1≤Btree ∧ 0≤Tclip ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(ψ:Fin 4→ℝ→ℂ),(∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))→
    ∀(D B v θ H m r η τ:ℝ),0≤η→η≤gap/50→τ≤gap/50→
      (∀i,hi i≤Z^η)→Z^(-η)≤lo 1→Tclip≤3*η*Real.log Z→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→B-θ+2*η≤U→
      radialCenter m H θ D B≤4*η+τ→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤ c₁→c₁≤bcap→1≤ c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ (windowSource p S ψ Z D B v θ H))
        (w∘erasePoint) Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  sorry

end SevenEighths.InverseInitialRetainedWindow

end

end OAI
end
