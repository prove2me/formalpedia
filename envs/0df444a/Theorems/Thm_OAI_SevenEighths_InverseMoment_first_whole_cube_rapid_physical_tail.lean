-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_first_whole_cube_rapid_physical_tail
-- name    : OAI.SevenEighths.InverseMoment.first_whole_cube_rapid_physical_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T22:33:33.734173+00:00
-- url     : https://prove2.me/theorems/18677e53-b647-4d5c-a790-ae8c66be281e
-- title:
--   Rapid decay of the first whole-cube physical tail
-- statement:
--   For every $\varepsilon>0$, reals $M_{\max},F_{\max}\ge0$, $\eta\ge0$, $\tau>0$ and every real `saving`, there are a finite set $s\subseteq\mathbb N\times\mathbb N$ and $C_t,C_m>0$ such that for every admissible configuration — a family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` with residue characteristic $\ne2$, a finite `pool`, an admissible `b : CubeCoordinates ι`, finite sets $C$ (disjoint from `b.support`), $D\subseteq C\cup$`cubePrincipalSupport …`, `extra₁`, `extra₂`, a nonzero ideal $f$, multiplicative $\Psi_1,\Psi_2$ bounded by 1, slot data (`slots`, pairwise disjoint `lists`, coefficients $a$ bounded by 1), tests $\mathrm{test}_1,\mathrm{test}_2$ bounded by $G_1,G_2\ge0$ and supported where `primeProductNorm p U` $\le Z^{r+\eta}$, a Schwartz $W$, and reals with $E\ge0$, $Z\ge1$, $0\le M\le M_{\max}$, $\ell,V\ge0$, $-\eta\le r$, $r+3\ell+V\le F_{\max}$, together with the size hypotheses listed in the Lean (on `primeProductNorm` of $C$, `extra₁`, `extra₂`, $D$, the norms of `eisEmbedding (primeProduct …)` and of `jLabel …`, and $N(f)\le Z^{V+\eta}$) — the norm of `firstLocalPhysicalTail` at frequency balls of radius $Z^{\texttt{firstPhysicalHeight}\,M\,r\,\ell\,V\,\delta(D)\,B\,j+12\eta+\tau}$ is at most
--   $$65536\,(C_m(EZ^{r+\eta})^{\varepsilon}G_1)(C_m(EZ^{r+\eta})^{\varepsilon}G_2)\,(C_t\,\textstyle\sup_s\text{seminorms}(W))\,Z^{-\mathrm{saving}}.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.first_whole_cube_rapid_physical_tail` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstRapidPhysicalTail.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B007

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_rapid_physical_tail (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤Mmax) (hFm:0≤Fmax)
    (heta:0≤eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤E → 0≤G₁ → 0≤G₂ → 1≤Z → 0≤M → M≤Mmax →
      0≤ell → 0≤V → -eta≤ r → r+3*ell+V≤Fmax →
      primeProductNorm p C≤Z^(r+eta) →
      primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤G₁) → (∀U,‖test₂ U‖≤G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤Z^(V+eta) → primeProductNorm p D≤Z^(delta D+eta) →
      Z^(B-eta)≤primeProductNorm p C →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      65536*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
