-- Prove2me | Theorems.Thm_LocalPF_Block_lemma_4_1
-- name    : LocalPF.Block.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:22.175984+00:00
-- url     : https://prove2.me/theorems/6df9091e-097a-43fb-94c2-8ef96816f9e8
-- title:
--   Lemma 4.1, p. 32 — if ν ≥ εγ and ν′ ≥ εγ′, then ‖ν − ν′‖ ≤ 2(1 − ε) + ε‖γ − γ′‖
-- statement:
--   Let $\nu,\nu',\gamma,\gamma'$ be probability measures on a measurable space and let $\varepsilon>0$ be such that $\nu(A)\ge\varepsilon\gamma(A)$ and $\nu'(A)\ge\varepsilon\gamma'(A)$ for every measurable set $A$. Then
--   $$\|\nu-\nu'\|\le 2(1-\varepsilon)+\varepsilon\|\gamma-\gamma'\|,$$
--   where $\|\mu-\mu'\|=\sup_{|f|\le1}|\mu(f)-\mu'(f)|$.
--
--   In particular, if $\gamma=\gamma'$ then $\|\nu-\nu'\|\le2(1-\varepsilon)$. The lemma is used to bound the entries $C_{ij}$ of Dobrushin's matrix from minorization conditions.
--
--   **Formalization Note** Stated on an arbitrary measurable space (the paper's spaces are Polish). The norm takes values in $[0,\infty]$. The hypotheses force $\varepsilon\le1$.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 32, Lemma 4.1

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Lemma 4.1 (p. 32). -/
theorem lemma_4_1 {S : Type*} [MeasurableSpace S] (ν ν' γ γ' : Measure S)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν'] [IsProbabilityMeasure γ]
    [IsProbabilityMeasure γ'] (ε : ℝ) (hε : 0 < ε)
    (hν : ∀ A, MeasurableSet A → ENNReal.ofReal ε * γ A ≤ ν A)
    (hν' : ∀ A, MeasurableSet A → ENNReal.ofReal ε * γ' A ≤ ν' A) :
    tv ν ν' ≤ ENNReal.ofReal (2 * (1 - ε)) + ENNReal.ofReal ε * tv γ γ' := by sorry

end LocalPF.Block
