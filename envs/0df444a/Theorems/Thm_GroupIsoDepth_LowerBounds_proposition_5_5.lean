-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_proposition_5_5
-- name    : GroupIsoDepth.LowerBounds.proposition_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:42:11.663287+00:00
-- url     : https://prove2.me/theorems/df835e87-d7b9-45bf-a9ac-b94de5f7d031
-- title:
--   Proposition 5.5 — $G_M\cong\mathbb Z_4^{\mathrm{rk} M}\times\mathbb Z_2^{2k-2\mathrm{rk} M}$; $M\mapsto(G_M,G_{I_r\oplus0})$ is an $\mathbb F_2$-affine projection reduction, one row per bit
-- statement:
--   Let $k\in\mathbb N$ and $M,N\in\mathrm{Mat}_k(\mathbb F_2)$.
--   1. $G_M$ is an abelian 2-group (of order $2^{2k}$) of exponent at most 4, with isomorphism type $G_M\cong(\mathbb Z_4)^{\mathrm{rank}(M)}\times(\mathbb Z_2)^{2k-2\,\mathrm{rank}(M)}$.
--   2. In particular $G_M\cong G_N\iff\mathrm{rank}(M)=\mathrm{rank}(N)$.
--   3. For each fixed $r\le k$, the map $M\mapsto(G_M,G_{I_r\oplus0_{k-r}})$ (the pair of labelled Cayley tables of order $n=4^k$) is a many-one reduction from the rank-$r$ predicate of Matrix Rank over $\mathbb F_2$ to Group Isomorphism — $(G_M,G_{I_r\oplus0_{k-r}})\in\mathrm{GpI}_n\iff\mathrm{rank}(M)=r$ — and it is an $\mathbb F_2$-affine projection in which each output bit depends on at most one row of $M$: for every input bit $v$ of the pair there are a row index $j$, $a\in\mathbb F_2^k$ and $c\in\mathbb F_2$ with $\mathrm{bit}_v(M)=c+\sum_i a_iM_{j,i}$ for all $M$.
--
--   Differences from the source:
--   - encoding: an Abelian 2-group of exponent at most 4 → ∀ g h, g * h = h * g; ∀ g, g ^ 4 = 1; Fintype.card (GM M) = 2 ^ (2k); reason: the three properties spelled out; the group structure itself is the CommGroup instance of the definition
--   - encoding: G_M ≅ (Z_4)^{rank M} × (Z_2)^{2k−2 rank M} → Nonempty (GM M ≃* Multiplicative ((Fin M.rank → ZMod 4) × (Fin (2k − 2·M.rank) → ZMod 2))); reason: Mathlib's additive groups made multiplicative; 2k − 2 rank M is never truncated since rank M ≤ k
--   - encoding: for each fixed r (with I_r ⊕ 0_{k−r}) → r ≤ k; reason: I_r ⊕ 0_{k−r} is only defined for r ≤ k
--   - reading: an F₂-affine projection reduction from Matrix Rank over F₂ from the rank r predicate to Group Isomorphism, in which each bit of the output depends on at most one row of M → (i) GpI (4^k) (pairBits M (Ir0 k r)) ↔ M.rank = r for all M; (ii) every input bit v of the pair equals c + Σ_i a_i M_{j,i} in ZMod 2 for one row j; reason: (i) is the many-one reduction (§3.1, p. 16), (ii) is affineness with one row; a bit that does not depend on M is the case a = 0
--   - encoding: the Cayley table of G_M 'in our chosen way of representing elements' (labelling not fixed) → label(u, z) = Σ_i u_i 2^i + Σ_j z_j 2^{k+j} ∈ [4^k]; entry (a, a') of the table is label(ofLabel a · ofLabel a') in 2k = ⌈log₂ 4^k⌉ bits; reason: the paper leaves the labelling open; this one realizes its proof (bit i < k is u_i, bit k + j is z_j)
--   - encoding: order n = 2^{2k} → n = 4 ^ k; reason: same numbers
--   - reading: a circuit deciding Group Isomorphism on tables of order n → correct on every one of the 2^{2N} bit strings, including invalid tables and out-of-range labels (the total language: both tables valid group tables and isomorphic); reason: §4.1 (p. 24): the paper solves 'the total GpI problem rather than the promise problem', and Lemma 4.2 checks that entries lie in [n]
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Proposition 5.5 (p. 37, PDF 38)

import Mathlib
import Definitions.Def_GroupIsoDepth_LowerBounds_CayleyTables
import Definitions.Def_GroupIsoDepth_LowerBounds_MatrixGroup

namespace GroupIsoDepth.LowerBounds

/-- Proposition 5.5 (printed p. 37, PDF 38). For `M ∈ Mat_k(𝔽₂)`:
1. `G_M` is an abelian 2-group (of order `2^{2k}`) of exponent at most 4, with isomorphism type
   `G_M ≅ (ℤ₄)^{rank M} × (ℤ₂)^{2k − 2 rank M}`;
2. `G_M ≅ G_N` if and only if `rank M = rank N`;
3. for each fixed `r`, the map `M ↦ (G_M, G_{I_r ⊕ 0_{k−r}})` (labelled tables of order `n = 4^k`)
   is a reduction from the rank-`r` predicate of Matrix Rank over `𝔽₂` to Group Isomorphism, and it
   is an `𝔽₂`-affine projection in which each output bit depends on at most one row of `M`: every
   input bit of the pair equals `c + Σ_i a_i M_{j,i}` over `𝔽₂` for a single row index `j`. -/
theorem proposition_5_5 (k : ℕ) :
    (∀ M : Matrix (Fin k) (Fin k) (ZMod 2),
      (∀ g h : GM M, g * h = h * g) ∧ (∀ g : GM M, g ^ 4 = 1) ∧
      Fintype.card (GM M) = 2 ^ (2 * k) ∧
      Nonempty (GM M ≃* Multiplicative ((Fin M.rank → ZMod 4) × (Fin (2 * k - 2 * M.rank) → ZMod 2)))) ∧
    (∀ M N : Matrix (Fin k) (Fin k) (ZMod 2), Nonempty (GM M ≃* GM N) ↔ M.rank = N.rank) ∧
    (∀ r : ℕ, r ≤ k →
      (∀ M : Matrix (Fin k) (Fin k) (ZMod 2), GpI (4 ^ k) (pairBits M (Ir0 k r)) ↔ M.rank = r) ∧
      (∀ v : PairVar (4 ^ k), ∃ j : Fin k, ∃ a : Fin k → ZMod 2, ∃ c : ZMod 2,
        ∀ M : Matrix (Fin k) (Fin k) (ZMod 2),
          (((pairBits M (Ir0 k r) v).toNat : ℕ) : ZMod 2) = c + ∑ i : Fin k, a i * M j i)) := by sorry

end GroupIsoDepth.LowerBounds
