-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_prohibited_singleton_words_le_catalog
-- name    : OAI.TwoPointCorrelations.prohibited_singleton_words_le_catalog
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:35.424493+00:00
-- url     : https://prove2.me/theorems/630dfaad-9c71-4637-a799-cd3fcf64f6e4
-- title:
--   Centered averages of words with many singleton labels are bounded by the weighted witness catalogue
-- statement:
--   Let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) with primes at most $B$; $s,n,D$ naturals; $F$ a finite set of words (lists of signed steps), each with a labelling of a finite type $\tau$ by $P\cup Q$, targets below the labels, a base, a weight $R\ge0$ depending only on the labelled residues, a cap $C\ge0$ with $R\le C$ and $C\cdot2^{|\tau|+\#\text{singletons}}\le A$ ($A\ge0$), labels lying in data.P and in the word's divisor-prime support, every step a pair of the family, every tuple prime of a step labelled, singleton labels occurring at a single position, length $+\,ns\le D$, and $nsJ<\#$singleton labels. Then
--
--   $$\sum_{\mathrm{main}\in F}\Big|\mathbb E_x\Big[\Pi_{\mathrm{main}}(x)\prod_{t\in\tau}\Big(\mathbf 1_{x(\mathrm{label}(t))=\mathrm{target}(t)}-\frac1{\mathrm{label}(t)}\Big)\,\mathcal A_{\mathrm{main}}(x)\Big]\Big|\le A\sum_{r=0}^{D}\sum_{d\in\texttt{WitnessRecord}(n,r)}\ \sum_{\substack{e\in\texttt{PrimeWordEncoding}(r,r(J+M),P,Q)\\ e\text{ witnesses }d}}\mathrm{wt}(e),$$
--
--   where $\Pi$ = `paddingWeightedFunction … main (R main)`, $\mathcal A$ = `attachedCatalogAvoidance data s B D main`, and the expectation is over `data.residueLaw B hB`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.prohibited_singleton_words_le_catalog`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open scoped Classical

theorem prohibited_singleton_words_le_catalog {h J M : ℕ} {τ : Type*} [Fintype τ]
    (data : ProhibitedPrimeFamily h J M) (B s n D : ℕ)
    (F : Finset (List SignedStep))
    (label : List SignedStep → τ → ↥(data.P ∪ data.Q))
    (target : List SignedStep → τ → Fin B) (base : ↥(data.P ∪ data.Q) → Fin B)
    (R : List SignedStep → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (C : List SignedStep → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < (label main t).val)
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ A)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hseen : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ wordDivisorPrimeSupport main)
    (hlabelP : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ data.P)
    (hmainpairs : ∀ main ∈ F, ∀ t ∈ main, (t.tuple, t.padding) ∈ data.pairs)
    (htupleCover : ∀ main ∈ F, ∀ (k : Fin main.length) (i : ↥(data.P ∪ data.Q)),
      i.val ∈ (main.get k).tuple.primeFactors → i ∈ univ.image (label main))
    (position : ∀ main, singletonLabels (label main) → ℕ)
    (hposition : ∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
      TuplePrimeAt main i.val v → v = position main i)
    (hD : ∀ main ∈ F, main.length + n * s ≤ D)
    (hn : ∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) :
    (∑ main ∈ F,
      |(data.residueLaw B hB).average (fun x =>
        paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (R main) x *
        (∏ t, ((if x (label main t) = target main t then (1 : ℝ) else 0) -
          ((label main t).val : ℝ)⁻¹)) * attachedCatalogAvoidance data s B D main x)|) ≤
      A * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (r.val * (J + M)) data.P data.Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J (fun d q => (d, q) ∈ data.pairs)
          then e.weight else 0 := by
  sorry

end OAI.TwoPointCorrelations
