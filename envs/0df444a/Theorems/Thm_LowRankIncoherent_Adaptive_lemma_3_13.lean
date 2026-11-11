-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_3_13
-- name    : LowRankIncoherent.Adaptive.lemma_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:02.487009+00:00
-- url     : https://prove2.me/theorems/05ec8099-9f66-49cd-9663-a84d00cd83eb
-- title:
--   Lemma 3.13 — weighted quadratic estimate with fresh conditioning
-- statement:
--   Use the standing dimensions $a=d_1$, $b=d_2$, $D=ab$, $b≥2$, $1≤r≤D$, and $a≤rb$. Let $σ$ be a state with $σ\succeq I_a/(2a)$ and $X$ any joint state. For $n≥1$ fresh Haar snapshots put $E_0=\widehat X-X$. Let $W$ be a fixed $D\times k$ matrix of rank at most $r$, independent of this batch. There is an absolute $c_B>0$ such that for $0<δ<1$, with probability at least $1-δ$,
--   $$\|Φ_σ(E_0WW^†E_0)^†(I_b)\|_∞^{1/2}≤c_B\|W\|_∞\sqrt a\left(\sqrt{\frac{rb+\log(4/δ)}n}+\frac{rb+\log(4/δ)}n\right).$$
--   The same constant and bound hold pointwise conditional on any earlier classical transcript determining $σ,X,W$, when the batch is fresh. The statement encodes this using arbitrary transcript-indexed families and their explicit fresh-batch laws. It supports weights chosen from a preceding batch without allowing a weight to depend on its own samples.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
--   - encoding: the weighted estimate also holds conditional on an earlier classical transcript with fresh measurements → the same universal constant bounds the fresh-batch law pointwise for every transcript-indexed family of states, inputs and weights; reason: the earlier transcript fixes these parameters, and the displayed conditional law is the independent product of their Haar/Born experiments
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 3.13, printed p. 25 = PDF p. 25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_3_13 : ∃ cB : ℝ, 0 < cB ∧
    ∀ (a b r k n : ℕ), 0 < a → 2 ≤ b → 1 ≤ r → r ≤ a*b → a ≤ r*b → 1 ≤ n →
    ∀ (Γ : Type) (σ : Γ → Input a) (X : Γ → Joint a b)
      (W : Γ → Matrix (Fin b × Fin a) (Fin k) ℂ),
    (∀ t, State (σ t) ∧ LE ((1/(2*(a : ℂ))) • 1) (σ t)) →
    (∀ t, State (X t)) → (∀ t, (W t).rank ≤ r) →
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t : Γ,
    (batchLaw (X t) n) {z |
      let E := estimate z - X t
      Real.sqrt (opNorm (adjointI (σ t) (E * W t * (W t)ᴴ * E))) ≤
        cB * opNorm (W t) * Real.sqrt a *
          (Real.sqrt ((r*b + Real.log (4/δ))/n) + (r*b + Real.log (4/δ))/n)}
      ≥ ENNReal.ofReal (1-δ) := by sorry

end LowRankIncoherent.Adaptive
