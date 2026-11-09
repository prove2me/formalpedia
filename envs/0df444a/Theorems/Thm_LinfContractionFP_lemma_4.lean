-- Prove2me | Theorems.Thm_LinfContractionFP_lemma_4
-- name    : LinfContractionFP.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:16.095204+00:00
-- url     : https://prove2.me/theorems/18ec1b6b-76bb-4b6d-ba6d-1ba2f6fd014d
-- title:
--   Lemma 4 — one boosting iteration either labels $R_\pm$ or keeps the budget valid
-- statement:
--   Consider one iteration of the boosting loop of Amplify$(b,\tau,F,B_+,B_-)$ with $\tau,B_\pm>0$, in which every recursive call returns a labeling satisfying Contract 1. If the iteration starts with $\Phi_+(F)\le B_+$ (and no coordinate of $R_+$ already labelled $-1$), then either
--
--   1. all coordinates of $R_+$ carry the label $+1$ after Step III (Line 14), or
--   2. the exponential weight of the coordinates of $S_+$ voted $-1$ on Line 15 is less than $\Phi_+(F)/4$, and $\Phi_+(F')\le\tfrac{\sqrt3}{2}B_+$ for the updated tallies $F'=F+\ell'$.
--
--   Symmetrically for $-1$ labels, $R_-$, $S_-$, $\Phi_-$ and $B_-$. This is the inductive step of Theorem 3.
--
--   Differences from the source:
--   - generalization: the recursive calls of Amplify on Lines 7, 10 and 15 → any procedure sub that either fails (none, a defeat, aborting the iteration) or returns labels satisfying Contract 1 at the tolerances τ/32 and τ/2, the conclusion holding for every iteration whose calls all returned labelings; reason: the paper's inductive hypothesis ('we focus on the case in which all recursive calls return labelings', p.16); Amplify's calls meet it by Theorem 3, so the statement specializes
--   - reading: an iteration of Algorithm 3 → an arbitrary label vector at the iteration's start, with no −1 on R₊ (resp. no +1 on R₋); reason: invariant of Algorithm 3: true at Line 3 and preserved since Line 13 never labels R₊ with −1 (proof, p.18)
--   - encoding: 'a symmetric result holds for the −1 labels' → both sides as two conjuncts; reason: the symmetric statement made explicit
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 4, p.17; proof pp.17–19

import Mathlib
import Definitions.Def_LinfContractionFP_Contract1
import Definitions.Def_LinfContractionFP_boostRound

open scoped Classical

namespace LinfContractionFP

/-- Lemma 4 (both sides): each iteration of the boosting loop of Algorithm 3 that starts with
`Φ₊(F) ≤ B₊` either (i) sets `+1` on all of `R₊` (Line 14), or (ii) makes the exponential weight
of the coordinates of `S₊` voted `−1` on Line 15 less than `Φ₊(F)/4`, so that `(√3/2)B₊` bounds
`Φ₊` after the tally update; symmetrically for `−1`, `R₋`, `S₋`, `Φ₋`, `B₋`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Lemma 4, p.17: "Lemma 4. Each iteration of the boosting loop (Line 4 in Algorithm 3) that
starts with Φ+(F) ≤ B+ either: (i) sets +1 labels to all coordinates in R+ via Line 14; or
(ii) guarantees that the sum of exponential weights of the misclassified +1 labels (i.e., labels
in S+ that were voted −1 instead of the correct +1 on Line 15) is less than 1/4 of Φ+(F). Thus,
the inductive contract of boosting (6) holds, and the updated bound B+ ← (√3/2)B+ remains a valid
upper bound for Φ+(F) at the next round." p.16: "(a symmetric result holds for the −1 labels
and is proved identically)".

**Formalization Note.** The iteration is `boostRound` (lines 5–15) run without counters in the
`Option` monad, its recursive calls replaced by any `sub` that either fails (`none`, a defeat of
Oracle, which aborts the iteration) or returns labels satisfying Contract 1 at the tolerances
`τ/32` and `τ/2` it is called with (the paper's inductive hypothesis, Theorem 3 on deeper
calls). The conclusion is about an iteration whose recursive calls all returned labelings
(`hr`): "we focus on the case in which all recursive calls return labelings", p.16. (A `sub`
that must return labels at every shift cannot exist: at a shift making all `σ'_i` equal,
Contract 1 asks for `+1` and `−1` on every coordinate.) `ℓ` is the label vector at the start of the
iteration; the hypothesis that no coordinate of `R₊` already carries `−1` is the invariant
Algorithm 3 maintains (true at Line 3, preserved because Line 13 never labels `R₊` with `−1`).
`F'` is the tally after Line 17. -/
theorem lemma_4 {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) (hτ : 0 < τ) (F : κ → ℤ)
    (Bp Bm : ℝ) (hBp : 0 < Bp) (hBm : 0 < Bm)
    (sub : (κ → ℝ) → ℝ → (κ → ℤ) → ℝ → ℝ → Option (κ → Lbl))
    (hsub : ∀ (b' : κ → ℝ) (τ' Bp' Bm' : ℝ) (ℓ' : κ → Lbl), (τ' = τ / 32 ∨ τ' = τ / 2) →
      0 < Bp' → 0 < Bm' → sub b' τ' F Bp' Bm' = some ℓ' → Contract1 σ b' τ' F Bp' Bm' ℓ')
    (ℓ : κ → Option Lbl) (r : RoundOut κ)
    (hr : boostRound (m := Option) (fun _ => pure ()) sub b τ F Bp Bm ℓ = some r) :
    let F' : κ → ℤ := fun i => F i + (r.weak i).val
    (phiPlus σ b τ F ≤ Bp → (∀ i ∈ bandRplus σ b τ, ℓ i ≠ some Lbl.lo) →
      (∀ i ∈ bandRplus σ b τ, r.labels i = some Lbl.hi) ∨
        ((∑ i ∈ bandSplus σ b τ with r.weak i = Lbl.lo, Real.sqrt 3 ^ (-(F i))) <
            phiPlus σ b τ F / 4 ∧
          phiPlus σ b τ F' ≤ Real.sqrt 3 / 2 * Bp)) ∧
      (phiMinus σ b τ F ≤ Bm → (∀ i ∈ bandRminus σ b τ, ℓ i ≠ some Lbl.hi) →
        (∀ i ∈ bandRminus σ b τ, r.labels i = some Lbl.lo) ∨
          ((∑ i ∈ bandSminus σ b τ with r.weak i = Lbl.hi, Real.sqrt 3 ^ (F i)) <
              phiMinus σ b τ F / 4 ∧
            phiMinus σ b τ F' ≤ Real.sqrt 3 / 2 * Bm)) := by sorry

end LinfContractionFP
