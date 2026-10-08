-- Prove2me | Theorems.Thm_HarmonicGames_GenericPure_proposition_4_1
-- name    : HarmonicGames.GenericPure.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:56.086982+00:00
-- url     : https://prove2.me/theorems/13bc2275-6ae3-4568-8439-2976cbdd6186
-- title:
--   Proposition 4.1 — dimensions of the potential, harmonic and nonstrategic subspaces
-- statement:
--   Consider games with $M$ players, where player $m$ has $h_m \ge 1$ strategies. The subspaces $\mathcal P$, $\mathcal H$, $\mathcal N$ of Definition 4.2 have dimensions
--
--   1. $\dim(\mathcal P) = \prod_{m\in\mathcal M} h_m - 1$,
--   2. $\dim(\mathcal H) = (M-1)\prod_{m\in\mathcal M} h_m - \sum_{m\in\mathcal M}\prod_{k\ne m} h_k + 1$,
--   3. $\dim(\mathcal N) = \sum_{m\in\mathcal M}\prod_{k\ne m} h_k$.
--
--   In particular, part 2 shows that $\dim \mathcal H > 0$ as soon as two players have at least two strategies each, which is how the proof of Proposition 5.1 uses it. The three dimensions add up to $M\prod_m h_m = \dim C_0^M$, as the direct sum decomposition $C_0^M = \mathcal P \oplus \mathcal H \oplus \mathcal N$ requires.
--
--   **Formalization Note** The three identities are stated as equalities of integers (dimensions cast to $\mathbb Z$), so that $M - 1$ and the subtraction in part 2 are not truncated as natural-number subtraction. Strategy sets are nonempty, as in the paper ($E^m = \{1,\dots,h_m\}$); with $M = 0$ all three formulas give $0$, which is correct for the one-profile game.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 19, Proposition 4.1

import Mathlib
import Definitions.Def_HarmonicGames_GenericPure_Games

namespace HarmonicGames.GenericPure

/-- **Proposition 4.1** (p. 19). With `M = |ι|` players and `h_m = |E^m| ≥ 1` strategies for
player `m`, the dimensions of the potential, harmonic and nonstrategic subspaces of (28) are
1. `dim P = ∏_m h_m − 1`,
2. `dim H = (M − 1) ∏_m h_m − ∑_m ∏_{k ≠ m} h_k + 1`,
3. `dim N = ∑_m ∏_{k ≠ m} h_k`.
All three are stated in `ℤ`, so that no natural-number subtraction truncates. -/
theorem proposition_4_1 {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] :
    (Module.finrank ℝ (potentialSubspace E) : ℤ) =
        (∏ m, (Fintype.card (E m) : ℤ)) - 1 ∧
      (Module.finrank ℝ (harmonicSubspace E) : ℤ) =
        ((Fintype.card ι : ℤ) - 1) * (∏ m, (Fintype.card (E m) : ℤ)) -
          (∑ m, ∏ k ∈ Finset.univ.erase m, (Fintype.card (E k) : ℤ)) + 1 ∧
      (Module.finrank ℝ (HarmonicGames.Decomposition.nonstrategicSubspace E) : ℤ) =
        ∑ m, ∏ k ∈ Finset.univ.erase m, (Fintype.card (E k) : ℤ) := by sorry

end HarmonicGames.GenericPure
