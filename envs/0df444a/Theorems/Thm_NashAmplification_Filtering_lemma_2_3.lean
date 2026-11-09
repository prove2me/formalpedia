-- Prove2me | Theorems.Thm_NashAmplification_Filtering_lemma_2_3
-- name    : NashAmplification.Filtering.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:20:33.734961+00:00
-- url     : https://prove2.me/theorems/8bd9584b-b3b9-4e75-83af-11c65a7c2be9
-- title:
--   Lemma 2.3 — sufficient condition for a multiplier of one
-- statement:
--   Let $Z$ be finite, $0<q<1$, $h>0$, $\rho(z)\ge0$, $w(z),v(z)\in[0,1]$, and $m=\sum_z\rho(z)w(z)>0$. Let $\theta$ be Filter's selected threshold. Suppose $v_0\in[0,1]$ and $L\subseteq Z$ satisfy
--   $$\sum_{z\in L}\rho(z)w(z)>(1-q)m,\qquad v_0-v(z)>h\quad(z\in L).$$
--   Then $\phi(v_0,\theta)=1$. This condition is the link between low-score mass and exact preservation of a high-scoring sequence's weight.
--
--   Differences from the source:
--   - generalization: Z=A^t and q,h derived from (2.5) → arbitrary finite Z, 0<q<1 and h>0; reason: these are exactly the conditions used in the filter proof and include every paper call
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Lemma 2.3, PDF p. 9 (printed p. 8)

import Definitions.Def_NashAmplification_Filtering_Filter

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Lemma 2.3, PDF 9, condition (2.9). -/
theorem lemma_2_3 {Z : Type} [Fintype Z] (q h : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hh : 0 < h) (ρ w v : Z → ℝ) (hρ : ∀ z, 0 ≤ ρ z)
    (hw : ∀ z, w z ∈ Set.Icc (0 : ℝ) 1) (hv : ∀ z, v z ∈ Set.Icc (0 : ℝ) 1)
    (hm : 0 < mass ρ w) (v₀ : ℝ) (hv₀ : v₀ ∈ Set.Icc (0 : ℝ) 1)
    (L : Finset Z) (hL : (1-q) * mass ρ w < ∑ z ∈ L, ρ z * w z)
    (hgap : ∀ z ∈ L, h < v₀ - v z) :
    phi h v₀ (threshold q h ρ w v) = 1 := by sorry
end NashAmplification.Filtering
