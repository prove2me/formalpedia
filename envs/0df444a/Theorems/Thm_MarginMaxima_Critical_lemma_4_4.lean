-- Prove2me | Theorems.Thm_MarginMaxima_Critical_lemma_4_4
-- name    : MarginMaxima.Critical.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:02:44.735453+00:00
-- url     : https://prove2.me/theorems/65c94567-ee9a-4abe-b5a4-cad51d5cfd31
-- title:
--   Lemma 4.4 — disjoint copies: $\lfloor r/r'\rfloor\ge r/(2r')$ orthogonal copies realize the union of the copies of $Y$ with $r$ heads
-- statement:
--   Let $Y$ be realized by $r'$ heads in a block system and let $r\ge r'\ge1$. Take $a=\lfloor r/r'\rfloor\ge r/(2r')$ copies of the system, with mutually orthogonal spaces $\mathcal L$ and the same $h_0$: copy $i$ has documents $\xi_{(i,y)}$ and block vectors $\ell_{(i,B)}$ equal to $\xi_y$, $\ell_B$ placed in the $i$-th orthogonal summand, and blocks $\{i\}\times B$. They form a block system with the same parameters in which the union $\{1,\dots,a\}\times Y$ of the copies of $Y$ is realized by $r$ heads.
--
--   Differences from the source:
--   - encoding: a block system: Hilbert space ℒ ⊥ h₀, documents ξ_y + κh₀, heads ℓ_B − κh₀ → BlockSystem L C β g s κ with L a complete real inner product space, blocks indexed by β, and scores ⟨ℓ, ξ_y⟩ − κ²; reason: ⟨ℓ − κh₀, ξ + κh₀⟩ = ⟨ℓ, ξ⟩ − κ² since ℓ, ξ ⊥ h₀ and ∥h₀∥ = 1; the same systems
--   - encoding: ⌊r/r′⌋ copies of the system with mutually orthogonal spaces ℒ and the same h₀ → ∃ S′ : BlockSystem on Fin (r/r′) × C over PiLp 2 (Fin (r/r′) → L) whose documents, block vectors and blocks are the copies Pi.single i ξ_y, Pi.single i ℓ_B, {i} × B; reason: the orthogonal direct sum of the copies; h₀ is shared through the common κ² term of the score
--   - encoding: ⌊r/r′⌋ ≥ r/(2r′); the union of the copies of Y → (r : ℝ)/(2r′) ≤ ((r / r′ : ℕ) : ℝ); Finset.univ ×ˢ Y; reason: ℕ division is the floor
--   - reading: r ≥ r′ (r′ the number of heads realizing Y) → 1 ≤ r′ ≤ r; reason: r′ is a positive number of heads (⌊r/r′⌋ needs r′ ≥ 1)
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 9, Lemma 4.4

import Mathlib
import Definitions.Def_MarginMaxima_Critical_BlockSystem

namespace MarginMaxima.Critical

theorem lemma_4_4 {L : Type} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [CompleteSpace L]
    {C β : Type} [DecidableEq C] {g s κ : ℝ}
    (S : BlockSystem L C β g s κ) (Y : Finset C) (r' r : ℕ) (hr' : 1 ≤ r') (hrr : r' ≤ r)
    (hY : S.Realizes Y r') :
    (r : ℝ) / (2 * r') ≤ ((r / r' : ℕ) : ℝ) ∧
      ∃ S' : BlockSystem (PiLp 2 fun _ : Fin (r / r') => L) (Fin (r / r') × C)
          (Fin (r / r') × β) g s κ,
        (∀ i y, S'.ξ (i, y) = WithLp.toLp 2 (Pi.single i (S.ξ y))) ∧
        (∀ i b, S'.ℓ (i, b) = WithLp.toLp 2 (Pi.single i (S.ℓ b))) ∧
        (∀ i b, S'.blk (i, b) = (S.blk b).image fun y => (i, y)) ∧
        S'.Realizes (Finset.univ ×ˢ Y) r := by sorry

end MarginMaxima.Critical
