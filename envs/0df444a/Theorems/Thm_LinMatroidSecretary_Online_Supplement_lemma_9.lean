-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_Supplement_lemma_9
-- name    : LinMatroidSecretary.Online.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:20.911496+00:00
-- url     : https://prove2.me/theorems/135ba1f8-3d0a-41e5-9867-6842bf8083da
-- title:
--   Lemma 9 — one subset rule for an entire chain
-- statement:
--   Let $F$ be a finite field, $V=F^d$, $0\le\alpha\le1$, and let $\nu$ be a subspace probability distribution satisfying
--   $$\mathbb E_{W\sim\nu}\dim(W\cap L)\le(1-\alpha)\dim L\qquad(L\le V).$$
--   Let $B$ be an independent bundle of a finite labelled vector family $v:E\to V$, and put $H=\langle B\rangle$. For every finite strictly increasing chain $L_1<\cdots<L_s\le V$, there exists one randomized rule, depending on the chain and the observed $W$, selecting $T\subseteq B$. Its conditional distributions are nonnegative, have mass one, and are supported on bundles with
--   $$\dim(W+\langle T\rangle)=\dim W+|T|,\qquad\Pr[b\in T]=\alpha\quad(b\in B).$$
--   For this same rule all the following inequalities hold simultaneously:
--   $$\mathbb E\dim((W+\langle T\rangle)\cap L_j)\le(1-\alpha)\dim L_j+\alpha\dim(H\cap L_j)\quad(1\le j\le s).$$
--   All expectations include both random choices. This is the chain-compatible form of bundle selection used in the feasibility argument for Lemma 7.
--
--   Differences from the source:
--   - encoding: an independent set of vectors in a finite-dimensional space over a finite field → a finite labelled family v : E → F^d, independent on the specified finite bundle, and a finitely supported law on subspaces; reason: independence makes the bundle labels injective on vectors; every finite-dimensional space has coordinates, and over a finite field every subspace law has finite support
--   - encoding: a chain L1 < ··· < Ls → a strictly increasing map L : Fin s → Submodule F (Fin d → F); reason: zero-based indexing only relabels the same finite chain; the empty chain leaves the complete selection assertion
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, Lemma 9, PDF p. 27 (printed p. 25)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Supplement_BundleLP

namespace LinMatroidSecretary.Online.Supplement

/-- Lemma 9, STOC 2027 #608, PDF p. 27 (printed p. 25). One rule simultaneously
satisfies the bound at every member of the chain, including the empty-chain case. -/
theorem lemma_9 {F : Type} [Field F] [Fintype F] {d : ℕ}
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ν : Dist F d)
    (hν : IsDistOn ν ⊤) (hDim : DimIneqAlpha ν α)
    {E : Type} [Fintype E] [DecidableEq E] (v : E → Fin d → F)
    (B : Finset E) (hB : LinearIndepOn F v (B : Set E))
    (s : ℕ) (L : Fin s → Submodule F (Fin d → F)) (hL : StrictMono L) :
    ∃ ρ : SelectionRule F d E, SelectionValid v ν B ρ ∧
      (∀ b ∈ B, selectionMarginal ν B ρ b = α) ∧
      ∀ j, selectionExpect ν B ρ (fun W T => dimInter (W ⊔ bundleSpan v T) (L j)) ≤
        (1 - α) * (Module.finrank F (L j) : ℝ) + α * dimInter (bundleSpan v B) (L j) := by sorry

end LinMatroidSecretary.Online.Supplement
