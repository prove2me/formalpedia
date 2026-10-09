-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseReflectedPhase_low_original_completed_energy
-- name    : OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:46:54.098964+00:00
-- url     : https://prove2.me/theorems/ba4d6403-1da7-40e3-8259-d13327bb7095
-- title:
--   Energy of low original completed rows with marked prime slots
-- statement:
--   Let $Q\ne0$ and squarefree $F$ be ideals of $\mathcal O$ (Eisenstein integers), $m\ne0$ with `goodLambda`$\mid m$, $2\mid m$, $Q\cdot(72)\mid(m)$ and every prime of `fixedBadPrimes` dividing $(m)F$; $W$ smooth with support in $[lo,hi]$, $lo>0$; $C_k>0$, $0<\eta\le1$ and $r_{\max}\in\mathbb N$. Then there are a degree $\in\mathbb N$ and $C>0$, $Z_0>1$ such that for every finite slot type $\sigma$ with at most $r_{\max}$ elements, all $Z\ge Z_0$, $0\le d\le1/6$, $0\le\ell_0\le1/6-d+\eta$, $|\mathrm{shift}|\le\eta$, every finite set `parents` of nonzero ideals of norm $\le C_kZ^{5/6-2d}$, pairwise disjoint `lists` of maximal prime ideals avoiding `goodLambda` with residue characteristic $\ne2$, bounds $H_i\ge1$ on their norms with $\prod_iH_i\le Z^{\ell_0}$, every multiplicative $\Psi$ bounded by 1 that `FactorsModulo Q`, every unit $u$, real $\theta$ and weights $w$ bounded by 1:
--   $$\sum_{I\in\mathrm{parents}}\Big\|\sum_{p}\Big(\prod_iw_i(p_i)\Big)\texttt{markedCompletedT}\big(\texttt{rowTwist}\,\Psi\,m\,F_{\mathrm{gen}}\,(uI_{\mathrm{gen}}),\ \texttt{normTwistedSource}\,W\,\theta,\ Z^{1+\ell_0+\mathrm{shift}},\ A\mapsto\textstyle\prod_i[p_i\mid A]\big)\Big\|^2\le C(1+|\theta|)^{\mathrm{degree}}Z^{5/6-2d+507\eta}.$$
--
--   Lean: `OAI.SevenEighths.InverseReflectedPhase.low_original_completed_energy` in `lean/OAI/NumberTheory/DirichletL/Reflection/LowOriginalEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B009

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

theorem low_original_completed_energy (Q : Ideal Eis) (hQ : Q≠0)
    (F : Ideal Eis) (hF : Squarefree F) (m : Eis) (hm : m≠0)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hperiod : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (Ck η : ℝ) (hCk : 0<Ck) (hη : 0<η) (hη1 : η≤1) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (Z d ell0 shift : ℝ), Z₀≤Z → 0≤d → d≤1/6 → 0≤ell0 → ell0≤1/6-d+η → |shift|≤η →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d)) →
      Fintype.card σ≤ rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^ell0 →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo Q Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈parents,
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(1+ell0+shift)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^((5/6-2*d)+507*η) := by
  sorry
end
end SevenEighths.InverseReflectedPhase

end OAI
end
