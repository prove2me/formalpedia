-- Prove2me | Theorems.Thm_GL2QFT_Supplement_theorem_3_7
-- name    : GL2QFT.Supplement.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:40:59.194084+00:00
-- url     : https://prove2.me/theorems/2a039778-bc4c-4a37-8869-7d8927604775
-- title:
--   Theorem 3.7 — along a multiplicity-free chain, $Q_n=\mathfrak F_G$ in the Gelfand–Tsetlin basis
-- statement:
--   Let $\{e\}=G_1<G_2<\dots<G_n=G$ be a chain of subgroups of a finite group $G$. At every level $m$ fix labels $\mu$ and representations $R_\mu$ of $G_m$ written in the bases indexed by the Bratteli paths $P(\mu)$, so that for $m\ge2$ the path basis of every $\mu$ is subgroup-adapted to $G_{m-1}$ ((35)), and fix left transversals $T_m$ of $G_{m-1}$ in $G_m$. Define $Q_1=\mathfrak F_{G_1}$ and, recursively,
--   $$Q_m=(U^m_{\rm Ind}\otimes I)\,(I_{\mathbb C[T_m]}\otimes Q_{m-1})\,\mathrm{Enc}_m,\qquad 2\le m\le n. \tag{44}$$
--   Then
--   $$Q_n=\mathfrak F_G ,$$
--   the Fourier transform (22) of $G$, whose output basis is the Gelfand–Tsetlin basis $|\mu,Q,R^*\rangle$ indexed by pairs of paths $Q,R\in P(\mu)$.
--
--   The theorem turns the one-step factorization of Lemma 3.5 into a recursive QFT along any multiplicity-free chain (Figure 6); its cost is the sum of the costs of the $n-1$ encodings and induction transforms.
--
--   **Formalization Note** Levels are numbered $k=m-1$, and $G_m$ is the subgroup `grp k` of $G$ with `grp N = ⊤`. The basis of a node at level $k+1$ is literally indexed by the pairs $(\lambda,P)$, $\lambda\in N^-(\mu)$, $P\in P(\lambda)$, so the output basis of $Q_n$ is the path basis.
--
--   Differences from the source:
--   - generalization: Gelfand–Tsetlin bases of complete systems of irreps along a multiplicity-free chain → any matrix representations (homomorphisms) at every level in path-indexed bases subgroup-adapted to the previous level; reason: the proof applies Lemma 3.5 at each level, which uses only (35) and multiplicativity; the paper's Gelfand–Tsetlin bases (Corollary B.7) are an instance
--   - encoding: levels $m=1,\dots,n$ → $k=0,\dots,N$ with $m=k+1$, the groups as subgroups of $G$; reason: indexing only
--   - encoding: the identification of Lemma 3.5 at each level, implicit in (44) → the rows of each $Q_m$ re-indexed by the published `ident`; reason: the same identification made explicit
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), Theorem 3.7, eq. (44), p.22 (PDF p.23); §3.3 p.21

import Definitions.Def_GL2QFT_Supplement_Chain

open Classical

namespace GL2QFT

namespace Supplement

open Induction Chain

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), **Theorem 3.7**, p.22 (PDF p.23): "Define
`Q_1 = F_{G_1} = I` and, recursively, define `Q_m = (U^m_Ind ⊗ I)(I_{ℂ[T_m]} ⊗ Q_{m−1}) Enc_m`,
`2 ≤ m ≤ n` (44). Then `Q_n = F_G`. Its output basis is the Gelfand–Tsetlin basis indexed by pairs
of paths in the Bratteli diagram."

Data (levels `k = 0, …, N`, the paper's `m = k + 1`, `n = N + 1`): a chain of subgroups
`{e} = grp 0 < grp 1 < ⋯ < grp N = G` of a finite group `G`; label sets `Λ k`; predecessor sets
`N⁻(μ) ⊆ Λ k` for `μ ∈ Λ (k+1)`; for each node a representation `R_μ` of `grp k` in the basis
indexed by the Bratteli paths `P(μ)` (the Gelfand–Tsetlin labels); left transversals `T_m` of
`grp k` in `grp (k+1)`. If every `R_μ` is a representation and the path basis of every node at level
`k + 1` is subgroup-adapted to `grp k` ((35)), then `Q_n` equals the Fourier transform (22) of `G`
in the Gelfand–Tsetlin basis, whose rows are the triples `(μ, Q, R)` with `Q, R ∈ P(μ)`.

**Formalization Note** `G_n = G` is the subgroup `grp N = ⊤`, so the columns of `Q_n` and of
`F_G` are the elements of `grp N`. As in the base mission's `lemma_3_5`, the families need not be
complete systems of irreps: the identity holds for any representations in subgroup-adapted path
bases, and the paper's Gelfand–Tsetlin bases of irreps are an instance. -/
theorem theorem_3_7 {G : Type} [Group G] [Fintype G] (N : ℕ) (grp : ℕ → Subgroup G)
    (h0 : grp 0 = ⊥) (hN : grp N = ⊤) (hchain : ∀ k < N, grp k < grp (k + 1))
    (Λ : ℕ → Type) [∀ k, Fintype (Λ k)] (Nm : ∀ k, Λ (k + 1) → Finset (Λ k))
    (R : ∀ k (μ : Λ k), grp k → Matrix (Paths Λ Nm k μ) (Paths Λ Nm k μ) ℂ)
    (hR : ∀ k ≤ N, ∀ μ, IsMatRep (R k μ))
    (hAd : ∀ k < N, IsSubgroupAdapted (lowerSub grp k) (Paths Λ Nm k) (Nm k)
      (fun l h => R k l (toLower grp k h)) (R (k + 1)))
    (T : ∀ k, Set (grp (k + 1)))
    (hT : ∀ k < N, Subgroup.IsComplement (T k) (lowerSub grp k : Set (grp (k + 1)))) :
    chainQ grp Λ Nm R T N = fourierMatrix (R N) := by sorry

end Supplement

end GL2QFT
