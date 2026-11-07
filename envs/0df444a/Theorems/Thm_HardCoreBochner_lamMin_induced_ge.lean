-- Prove2me | Theorems.Thm_HardCoreBochner_lamMin_induced_ge
-- name    : HardCoreBochner.lamMin_induced_ge
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:31:47.648561+00:00
-- url     : https://prove2.me/theorems/8183cbdb-9378-4f72-9f0a-8d5a1084ee81
-- title:
--   Proof of Theorem 1.1 — interlacing $\lambda_{\min}(A_{G[S]})\ge\lambda_{\min}(A_G)$
-- statement:
--   Let $G$ be a finite simple graph and $S$ any set of its vertices. The minimum eigenvalue of the principal submatrix of $A_G$ on $S$, which is the adjacency matrix of the induced subgraph $G[S]$, is at least that of $A_G$:
--   $$\lambda_{\min}\big(A_{G[S]}\big)\ \ge\ \lambda_{\min}(A_G).$$
--   In particular $\lambda_{\min}(A_{G_\sigma})\ge\lambda_{\min}(A_G)$ for every independent set $\sigma$, which is how the proof of Theorem 1.1 verifies hypothesis (3) at every $\sigma$ from a condition on $G$ alone.
--
--   **Formalization Note** For $S=\emptyset$ the left side is the empty infimum $0$, and the statement reads $\lambda_{\min}(A_G)\le 0$, which holds because $A_G$ has trace $0$.
--
--   Differences from the source:
--   - generalization: λ_min(A_{G_σ}) ≥ λ_min(A_G) for G_σ, the graph left after removing σ and its neighbours → lamMin G ≤ λ_min of the principal submatrix of A_G on any S : Finset V; reason: G_σ is the induced subgraph on V(G_σ), whose adjacency matrix is the principal submatrix on S = V(G_σ)
--   - encoding: λ_min of the empty matrix (S = ∅, i.e. G_σ empty) → 0 (empty real infimum); reason: the statement then says λ_min(A_G) ≤ 0, which is true; no instance with S ≠ ∅ is affected
-- source:
--   Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, A simple proof of rapid mixing on random regular graphs beyond uniqueness, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b6107de9702dda27883f2839093b816f7a6f9c543fcb2be0ad91ad6ad), proof of Theorem 1.1, p.4 (PDF p.4)

import Definitions.Def_HardCoreBochner_lamMin

namespace HardCoreBochner

/-- **Eigenvalue interlacing for principal submatrices.** Göbel, Jenssen, Michelen, Pappik, Perkins, Schiller, *A simple proof of rapid mixing on random
regular graphs beyond uniqueness*, arXiv:2606.27545 (version of 2026-11-03, sha256 dfc58c3b…), proof of Theorem 1.1, p.4: "By
eigenvalue interlacing we note that λmin(AGσ) ≥ λmin(AG)."

For every set `S` of vertices of `G`, the minimum eigenvalue of the principal submatrix of `A_G` on
`S` (the adjacency matrix of the induced subgraph `G[S]`) is at least `λ_min(A_G)`. The printed claim
is the case `S = V(G_σ)`.

**Formalization Note** The principal submatrix is `Matrix.submatrix` along `S ↪ V`, and its minimum
eigenvalue is the published `BlockBochner.lamMin` (infimum of the real spectrum). For `S = ∅` the
spectrum is empty and the right side is `0`, and the claim then says `λ_min(A_G) ≤ 0` (true: `A_G` has trace
`0`). -/
theorem lamMin_induced_ge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    lamMin G ≤
      BlockBochner.lamMin ((G.adjMatrix ℝ).submatrix (fun i : S => (i : V)) (fun i : S => (i : V))) := by sorry

end HardCoreBochner
