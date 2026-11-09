-- Prove2me | Theorems.Thm_LinfContractionFP_lemma_3
-- name    : LinfContractionFP.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:16:46.369641+00:00
-- url     : https://prove2.me/theorems/940c6a29-6cbe-4c8e-b2b2-483ef876b59c
-- title:
--   Lemma 3 — the decoding rule (8) is correct once $B_+B_-<1$
-- statement:
--   Let $B_+,B_->0$ with $B_+B_-<1$ and consider the decoding rule
--   $$\ell_i=\begin{cases}+1&\text{if }3^{F_i}\ge B_-/B_+,\\-1&\text{otherwise.}\end{cases}$$
--   If $\Phi_+(F)\le B_+$, the rule assigns $+1$ to every $i\in S_+$; if $\Phi_-(F)\le B_-$, it assigns $-1$ to every $i\in S_-$.
--
--   This is how Amplify finishes: once the budgets' product drops below one, the signs of the tallies are correct.
--
--   Differences from the source:
--   - reading: Lemma 3 does not repeat B± > 0 → hypotheses 0 < B₊, 0 < B₋; reason: standing input condition of Algorithm 3 ('potential bounds B± > 0', p.15) under which Lemma 3 is used
-- source:
--   Soleymani–Farina, A Quasipolynomial Algorithm for ℓ∞ Contractions, arXiv:2610.30122 (held version, sha256 595b44934c28fc12e2cc9cb0fb7c0750d40a24fcd5661627726f3915a24cc0de), Lemma 3, p.14

import Mathlib
import Definitions.Def_LinfContractionFP_potentials
import Definitions.Def_LinfContractionFP_decode

namespace LinfContractionFP

/-- Lemma 3: if `B₊B₋ < 1`, the decoding rule (8) assigns `+1` to all of `S₊` when
`Φ₊(F) ≤ B₊`, and `−1` to all of `S₋` when `Φ₋(F) ≤ B₋`.

Soleymani–Farina, *A Quasipolynomial Algorithm for ℓ∞ Contractions*, arXiv:2610.30122 (held
version, sha256 595b4493…), Lemma 3, p.14: "Lemma 3. Assume that B+B− < 1, and consider the decoding rule for labels
ℓ_i := +1 if 3^{F_i} ≥ B−/B+; −1 otherwise. (8) If Φ+(F) ≤ B+, the labels assign +1 to all
i ∈ S+; similarly, if Φ−(F) ≤ B−, the labels assign −1 to all i ∈ S−."

**Formalization Note.** `B₊, B₋ > 0` is the standing input condition of Algorithm 3
("potential bounds B± > 0", p.15). The bands and potentials are those of `σ + b` at tolerance
`τ`. `+1` is `hi`, `−1` is `lo`. -/
theorem lemma_3 {κ : Type} [Fintype κ] (σ b : κ → ℝ) (τ : ℝ) (F : κ → ℤ) (Bp Bm : ℝ)
    (hBp : 0 < Bp) (hBm : 0 < Bm) (hB : Bp * Bm < 1) :
    (phiPlus σ b τ F ≤ Bp → ∀ i ∈ bandSplus σ b τ, decode F Bp Bm i = Lbl.hi) ∧
      (phiMinus σ b τ F ≤ Bm → ∀ i ∈ bandSminus σ b τ, decode F Bp Bm i = Lbl.lo) := by sorry

end LinfContractionFP
