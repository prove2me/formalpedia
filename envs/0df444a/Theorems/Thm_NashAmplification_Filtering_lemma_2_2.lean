-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_2_2
-- name    : NashAmplification.Filtering.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:02.9622+00:00
-- url     : https://prove2.me/theorems/9724b06b-0b08-4508-b11b-0bf861c09df8
-- title:
--   Lemma 2.2 — well-definedness and mass reduction
-- statement:
--   Let $Z$ be a finite set, $0<q<1$, $h>0$, $\rho(z)\ge0$, $w(z),v(z)\in[0,1]$, and $m=\sum_z\rho(z)w(z)>0$. The threshold returned by Filter is the smallest solution in $[-h,1]$ of its defining mass equation, and the updated weights satisfy
--   $$0\le w^+(z)\le w(z)\le1\quad(z\in Z),\qquad\sum_z\rho(z)w^+(z)=qm.$$
--   The conclusion asserts existence as well as minimality of the threshold. It establishes the validity and mass identity used at every round.
--
--   Differences from the source:
--   - generalization: Z=A^t and q,h derived from (2.5) → arbitrary finite Z, 0<q<1 and h>0; reason: these are exactly the conditions used in the filter proof and include every paper call
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 2.2, PDF p. 9 (printed p. 8)

import Definitions.Def_NashAmplification_Filtering_Filter

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 2.2, PDF 9: IsLeast includes the well-definedness claim. -/
theorem lemma_2_2 {Z : Type} [Fintype Z] (q h : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hh : 0 < h) (ρ w v : Z → ℝ) (hρ : ∀ z, 0 ≤ ρ z)
    (hw : ∀ z, w z ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ z, v z ∈ Set.Icc (0 : ℝ) 1)
    (hm : 0 < mass ρ w) :
    IsLeast (thresholdSet q h ρ w v) (threshold q h ρ w v) ∧
    (∀ z, 0 ≤ filterWeights q h ρ w v z ∧
      filterWeights q h ρ w v z ≤ w z ∧ w z ≤ 1) ∧
    mass ρ (filterWeights q h ρ w v) = q * mass ρ w := by sorry
end NashAmplification.Filtering
