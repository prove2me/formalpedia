-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_lemma_5_8
-- name    : GroupIsoDepth.LowerBounds.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:42:25.489385+00:00
-- url     : https://prove2.me/theorems/c47952e0-bba5-4f84-ab23-afd8a4c29cce
-- title:
--   Lemma 5.8 — on the pairs $(G_M,G_{I_r\oplus0_{k-r}})$, every CNF clause's falsifying set is a row-cube
-- statement:
--   Fix $r\le k\in\mathbb N$. Restrict inputs to the family of pairs of multiplication tables $\{(G_M,G_{I_r\oplus0_{k-r}}):M\in\mathrm{Mat}_k(\mathbb F_2)\}$ (tables of order $n=4^k$). Then for every clause $\Gamma$ over the $2n^2\lceil\log_2 n\rceil$ input bits, the falsifying set $\{M:\Gamma(G_M,G_{I_r\oplus0_{k-r}})=0\}$ has the form $A_1\times\dots\times A_k$, where each $A_j\subseteq\mathbb F_2^k$ is an affine subspace of possible choices for row $j$ of $M$; it is a row-cube.
--
--   Differences from the source:
--   - encoding: each A_j ⊆ F₂^k an affine subspace → A_j : AffineSubspace (ZMod 2) (Fin k → ZMod 2), which may be ⊥ (empty); reason: a clause with a literal that is true on the whole family has an empty falsifying set; the empty row-cube needs an empty factor
--   - encoding: a CNF clause → LiftSAParity.Clause (PairVar (4^k)), a Finset of literals; falsified when every literal is false; reason: the published clause object; a clause is an OR of literals
--   - encoding: the Cayley table of G_M 'in our chosen way of representing elements' (labelling not fixed) → label(u, z) = Σ_i u_i 2^i + Σ_j z_j 2^{k+j} ∈ [4^k]; entry (a, a') of the table is label(ofLabel a · ofLabel a') in 2k = ⌈log₂ 4^k⌉ bits; reason: the paper leaves the labelling open; this one realizes its proof (bit i < k is u_i, bit k + j is z_j)
--   - encoding: order n = 2^{2k} → n = 4 ^ k; reason: same numbers
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Lemma 5.8 (p. 38, PDF 39)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables
import Definitions.Def_GroupIsoDepth_LowerBounds_MatrixGroup
import Definitions.Def_GroupIsoDepth_LowerBounds_RowCubes

open LiftSAParity

namespace GroupIsoDepth.LowerBounds

/-- Lemma 5.8 (printed p. 38, PDF 39). Fix `r ≤ k`. Restricted to the pairs of tables
`(G_M, G_{I_r ⊕ 0_{k−r}})`, `M ∈ Mat_k(𝔽₂)`, the falsifying set of every clause over the input bits
is a row-cube `A₁ × ⋯ × A_k`, with each `A_j ⊆ 𝔽₂^k` an affine subspace of choices for row `j`. -/
theorem lemma_5_8 (r k : ℕ) (hrk : r ≤ k) (C : Clause (PairVar (4 ^ k))) :
    ∃ A : Fin k → AffineSubspace (ZMod 2) (Fin k → ZMod 2),
      {M : Matrix (Fin k) (Fin k) (ZMod 2) | Falsifies (pairBits M (Ir0 k r)) C} = rowCube A := by sorry

end GroupIsoDepth.LowerBounds
