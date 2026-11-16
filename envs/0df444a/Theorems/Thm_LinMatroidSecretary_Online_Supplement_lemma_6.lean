-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_Supplement_lemma_6
-- name    : LinMatroidSecretary.Online.Supplement.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:41.764978+00:00
-- url     : https://prove2.me/theorems/57ce74c8-b747-445c-89af-9aebe34a455c
-- title:
--   Lemma 6 — independent bundle selection with exact marginals
-- statement:
--   Let $F$ be a finite field, $V=F^d$, $0\le\alpha\le1$, and let $\nu$ be a probability distribution on subspaces of $V$. Suppose that
--   $$\mathbb E_{W\sim\nu}\dim(W\cap L)\le(1-\alpha)\dim L\qquad\text{for every }L\le V.$$
--   Let $C$ be an independent bundle in a finite labelled vector family $v:E\to V$. There exists a randomized rule that, after observing $W$, chooses $R\subseteq C$, with a nonnegative conditional distribution of total mass one for each positive-mass $W$, such that
--   $$\dim(W+\langle R\rangle)=\dim W+|R|\quad\text{almost surely},\qquad\Pr[c\in R]=\alpha\quad(c\in C).$$
--   The probability averages over both $W$ and the conditional subset choice. Empty bundles and the endpoints $\alpha=0,1$ are included. This is the subset-selection result needed for bundle arrivals.
--
--   Differences from the source:
--   - encoding: an independent set of vectors in a finite-dimensional space over a finite field → a finite labelled family v : E → F^d, independent on the specified finite bundle, and a finitely supported law on subspaces; reason: independence makes the bundle labels injective on vectors; every finite-dimensional space has coordinates, and over a finite field every subspace law has finite support
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, Lemma 6, PDF p. 22 (printed p. 20)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Supplement_BundleLP

namespace LinMatroidSecretary.Online.Supplement

/-- Lemma 6, STOC 2027 #608, PDF p. 22 (printed p. 20). All clauses of the
conditional subset selection rule are asserted, with exact marginal α. -/
theorem lemma_6 {F : Type} [Field F] [Fintype F] {d : ℕ}
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ν : Dist F d)
    (hν : IsDistOn ν ⊤) (hDim : DimIneqAlpha ν α)
    {E : Type} [Fintype E] [DecidableEq E] (v : E → Fin d → F)
    (C : Finset E) (hC : LinearIndepOn F v (C : Set E)) :
    ∃ ρ : SelectionRule F d E, SelectionValid v ν C ρ ∧
      ∀ c ∈ C, selectionMarginal ν C ρ c = α := by sorry

end LinMatroidSecretary.Online.Supplement
