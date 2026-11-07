-- Prove2me | Theorems.Thm_MMSDelta2_lemma_7_2
-- name    : MMSDelta2.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:42.090991+00:00
-- url     : https://prove2.me/theorems/ce79f05a-7c12-47be-bfbe-3d5802896638
-- title:
--   Lemma 7.2 — $c(S)=B$ exactly for the encodings of solutions, with $\omega(S)=\mathrm{score}$
-- statement:
--   Fix a 4-PARTITION instance $(W=\{a_1,\dots,a_{4\ell}\},T)$. A set $S\subseteq M_{asg}$ of assignment goods satisfies $c(S)=B$ if and only if there is a solution $\mathcal S=(S_1,\dots,S_\ell)$ of the instance with
--
--   $$S=\{h_{i,j}: a_i\in S_j,\ j\in[\ell]\}.$$
--
--   Under this correspondence, $\omega(S)=\mathrm{score}(\mathcal S)$.
--
--   The consistency numbers thus encode feasibility, and the weights encode the score, within one subset of assignment goods.
--
--   Differences from the source:
--   - encoding: S ⊆ M_asg and a solution 𝒮 = (S₁, …, S_ℓ) → S : Finset (Fin (4ℓ) × Fin ℓ) and σ with S = {(i, j) : σ i = j}; reason: (i, j) is h_{i+1, j+1}; σ i = j iff a_{i+1} ∈ S_{j+1}
--   - generalization: the §7 standing assumption: (W, T) is a LexMax4Partition-Promise instance, promised to admit a solution (p.27) → no promise: the statement holds for every 4-PARTITION instance I; reason: the proof (p.28–29) uses no solution; promise instances are a special case
-- source:
--   Gupta, Seetharaman, The Existence of Maximin Share Allocations is Δ₂ᴾ-complete, arXiv:2609.15841 (held version, sha256 a43b06b9…), Lemma 7.2, p.28 (PDF p.30)

import Mathlib
import Definitions.Def_MMSDelta2_Parameters

namespace MMSDelta2

/-- **Lemma 7.2**, p.28 (PDF p.30).

S. Gupta, S. Seetharaman, *The Existence of Maximin Share Allocations is Δ₂ᴾ-complete*,
arXiv:2609.15841 (held version, sha256 a43b06b9…).

A subset `S ⊆ M_asg` satisfies `c(S) = B` if and only if there is a solution `𝒮 = (S_1, …, S_ℓ)`
of the source instance with `S = {h_{i,j} : a_i ∈ S_j, j ∈ [ℓ]}`. Under this correspondence,
`ω(S) = score(𝒮)`.

**Formalization Note.** A set of assignment goods is `S : Finset (Fin (4ℓ) × Fin ℓ)` (`(i, j)` is
`h_{i+1,j+1}`); a solution is `σ` with `σ i = j` iff `a_{i+1} ∈ S_{j+1}`, so the set it
corresponds to is `{(i, j) : σ i = j}`. -/
theorem lemma_7_2 (I : FourPartInstance) (S : Finset (Fin (4 * I.q) × Fin I.q)) :
    (I.cSum S = I.B ↔
      ∃ σ, I.IsSolution σ ∧ S = Finset.univ.filter (fun p => σ p.1 = p.2)) ∧
    (∀ σ, I.IsSolution σ → S = Finset.univ.filter (fun p => σ p.1 = p.2) →
      I.omegaSum S = I.score σ) := by sorry

end MMSDelta2
