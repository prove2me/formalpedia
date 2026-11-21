-- Prove2me | Theorems.Thm_MasulloAudit_normalized_markushevich_not_schauder
-- name    : MasulloAudit.normalized_markushevich_not_schauder
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:48:26.607586+00:00
-- url     : https://prove2.me/theorems/645b5b17-9975-4b01-bfce-3bf3113b127e
-- title:
--   A normalized Markushevich basis of real Hilbert space which is not a Schauder basis
-- statement:
--   There are unit vectors in real ℓ² and continuous biorthogonal functionals such that the vectors span a dense subspace and the functionals separate points, yet the given sequence is not the vector sequence of any classical Schauder basis. Thus these vectors form a normalized Markushevich basis.
--
--   In the Markushevich case of Lemma 10.4.2.5 take the closed quotient kernel to be zero and the prescribed dense subspace to be the whole space. Every lift is then forced. The assertion in the sentence after (10.4.2.18) that the lifts form a Schauder basis of their closed span fails in this generality. The two displayed lifting conclusions (biorthogonality and norm bounds) still hold in this example. This does not determine whether the particular spectral system in Chapter 10 has stronger properties.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Lemma 10.4.2.5, pp. 461–462; Remarks 10.4.2.6–7; the proof of Theorem 10.4.2.8 invokes the lemma on p. 464. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib.Analysis.InnerProductSpace.l2Space

open Set

theorem MasulloAudit.normalized_markushevich_not_schauder :
    ∃ (u : ℕ → lp (fun _ : ℕ => ℝ) 2) (g : ℕ → lp (fun _ : ℕ => ℝ) 2 →L[ℝ] ℝ),
      (∀ i, ‖u i‖ = 1) ∧ (∀ i j, g i (u j) = if i=j then 1 else 0) ∧
      (Submodule.span ℝ (range u)).topologicalClosure = ⊤ ∧
      (∀ x, (∀ i, g i x = 0) → x = 0) ∧
      ¬∃ b : SchauderBasis ℝ (lp (fun _ : ℕ => ℝ) 2), ∀ i, b i = u i := by sorry
