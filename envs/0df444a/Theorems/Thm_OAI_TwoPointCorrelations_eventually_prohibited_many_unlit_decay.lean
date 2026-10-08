-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_many_unlit_decay
-- name    : OAI.TwoPointCorrelations.eventually_prohibited_many_unlit_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:15.514655+00:00
-- url     : https://prove2.me/theorems/26d37f6b-56ff-44b1-9f8b-2b150c1ba21d
-- title:
--   Words with many unlit occurrences contribute at most exp(−L^{101/100})
-- statement:
--   Let $C,C_e,C_s\ge0$. For all sufficiently large $L$: let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with primes at most $B$; $F$ a finite set of signed step words of length $R$, with labels, base, weights and caps; external, $H$ reals. Suppose $1\le R\le2L$, $S+RJ\le C_sL\log L$, $J+M\le C\log L$, $R(J+M)+1\le L^2$, $R+1\le L^2$, $0\le$ external $\le e^{C_eL}$, $\sum_{p\in\mathrm{data}.P}1/p\le L^2$, $\sum_{p\in\mathrm{data}.Q}1/p\le L^2$, $M\le100\log L$, $H\ge\exp(L^{199/200})$ and every prime of data.P is at least $H$; every step of every word is a pair of the family whose tuple has exactly the labelled primes as prime factors; caps $\ge0$, weights in $[0,\mathrm{cap}]$, nonzero only where `MainPaddingTests` hold; and $\mathrm{cap}(w)\,2^{\#\text{singleton labels}}\le$ `crudeTraceWeight R S (paddings of w) L external`. Then
--
--   $$\sum_{a\in\texttt{largeUnlitCatalog}\,F\,\mathrm{label}\,L}\texttt{prohibitedDesignatedTerm}(\mathrm{data},s,D,a_1,\mathrm{label}(a_1),\mathrm{base},\mathrm{weight}(a_1),a_2)\le\exp(-L^{101/100}).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.eventually_prohibited_many_unlit_decay`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem eventually_prohibited_many_unlit_decay (C Ce Cs : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop, ∀ (R J M S B h s D : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (Fin R → SignedStep) → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (Fin R → SignedStep) → ℝ) (external H : ℝ),
      1 ≤ R → (R : ℝ) ≤ 2 * L →
      ((S + R * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((R * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ p ∈ data.P, H ≤ p) →
      (∀ w ∈ F, ∀ i, ((w i).tuple, (w i).padding) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i, (w i).tuple.primeFactors = univ.image (fun j => (label w (i, j)).val)) →
      (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) →
      (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B (List.ofFn w) x) →
      (∀ w ∈ F, cap w * 2 ^ (singletonLabels (label w)).card ≤
        crudeTraceWeight R S (fun i => (w i).padding) L external) →
      (∑ a ∈ largeUnlitCatalog F label L,
        prohibitedDesignatedTerm data hB s D (List.ofFn a.1) (label a.1) base (weight a.1) a.2) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
