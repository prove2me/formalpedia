-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_first_global_retained_push_uniform
-- name    : OAI.SevenEighths.InverseMoment.first_global_retained_push_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:37:09.554143+00:00
-- url     : https://prove2.me/theorems/6d9de13a-8f9f-4260-80ee-4049e0cdf149
-- title:
--   Uniform push of the first global retained energy
-- statement:
--   For every $\varepsilon>0$ there is $K>0$ such that for all types $\iota,\kappa$ with decidable equality, every family $p:\iota\to\mathcal O$ of nonzero Eisenstein integers generating maximal, pairwise coprime ideals, injective as ideals, avoiding `goodLambda`, of residue characteristic $\ne2$ and with `goodLambda`$^2\mid p_i-1$, every finite $F\subseteq\iota$, finite `outer` $\subseteq\kappa$, `cube : κ → CubeCoordinates ι`, `common : κ → Finset ι`, multiplicative $\Psi_1,\Psi_2$ bounded by 1, $m_1,m_2\in\mathcal O$, $d:\kappa\to\mathcal O$, `labels : κ → Finset (Ideal O)` of nonzero squarefree ideals, coefficients $a$ bounded by $\Gamma\ge0$ on `firstRetainedSource p (labels k) (cube k) Y` ($Y>0$), every sign `negative`, $H$, `selector`, $\omega$, $X>0$ and $t$: the `firstFamilyEnergy` of the `firstGlobalRetainedSource` with coefficients `firstCanonicalCoefficient` and weights `retainedCubeWeight` is at most
--   $$\Gamma\,K\,Y^{\varepsilon}\sum_{k\in\mathrm{outer}}\texttt{firstCanonicalSecondEnergy}(\dots,k,\dots,\omega,X,t,Y).$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.first_global_retained_push_uniform` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstOriginalProfileUniform.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B007

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
open InverseAmbientProfileTower

theorem first_global_retained_push_uniform (ε:ℝ)(hε:0<ε):
    ∃ K:ℝ,0<K ∧ ∀ {ι κ:Type*} [DecidableEq ι] [DecidableEq κ] (p:ι→Eis)(hp:∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (F:Finset ι)(outer:Finset κ)(cube:κ→CubeCoordinates ι)(common:κ→Finset ι)
    (Ψ₁ Ψ₂:Eis→*ℂ)(m₁ m₂:Eis)(d:κ→Eis)
    (labels:κ→Finset (Ideal Eis))(a:κ→Ideal Eis×Eis→ℂ)(Γ Y:ℝ),
    (∀u,‖Ψ₁ u‖≤1)→(∀u,‖Ψ₂ u‖≤1)→0≤Γ→0<Y→
    (∀k∈outer,∀f∈labels k,Squarefree f)→(∀k∈outer,∀f∈labels k,f≠0)→
    (∀k∈outer,∀x∈firstRetainedSource p (labels k) (cube k) Y,‖a k x‖≤Γ)→
    ∀(negative:Bool)(H selector:κ→Finset ι→ℂ)(ω:ℝ→ℂ)(X t:ℝ),0<X→
    firstFamilyEnergy p hg (firstGlobalRetainedSource p outer labels cube Y) F
      (fun x=>selector x.1)
      (fun x=>firstCanonicalCoefficient p hp hcop hg (cube x.1) (common x.1) negative
        (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d x.1) (H x.1) x.2)
      (fun x=>retainedCubeWeight p hp hcop hg (cube x.1) (common x.1) Ψ₁ Ψ₂ m₁ m₂
        (d x.1) (a x.1) x.2)
      negative ω X t (fun x=>x.2.2) ≤
    Γ*K*Y^ε*∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj F (cube k) (common k)
      negative (if negative then Ψ₁ else Ψ₂) (if negative then m₁ else m₂) (d k)
      (H k) (selector k) ω X t Y := by
  sorry

end
end SevenEighths.InverseMoment

end OAI
end
