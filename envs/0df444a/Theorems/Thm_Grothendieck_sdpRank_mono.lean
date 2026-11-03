-- Prove2me | Theorems.Thm_Grothendieck_sdpRank_mono
-- name    : Grothendieck.sdpRank_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T16:08:54.303985+00:00
-- url     : https://prove2.me/theorems/e1b5ad9c-d97d-4b7a-be4d-6b35279b1f5a
-- title:
--   $\mathrm{SDP}_r(G,A)$ is monotone in the rank
-- statement:
--   For a finite graph $G$, a symmetric matrix $A$ and ranks $1\le r\le r'$,
--
--   $$
--   \mathrm{SDP}_r(G,A)\ \le\ \mathrm{SDP}_{r'}(G,A),
--   $$
--
--   so the rank-constrained optima increase with the rank and the Grothendieck constants $K(r,G)$ decrease.
--
--   The reason is an isometry: a unit family $f:V\to S^{r-1}$ becomes a unit family into $S^{r'-1}$ by appending $r'-r$ zero coordinates, and that embedding preserves every inner product $f(u)\cdot f(v)$. Hence the feasible set for rank $r$ sits inside the feasible set for rank $r'$ after applying the embedding, and the objective is unchanged, so the supremum can only grow.
--
--   The paper uses this without comment when it treats $\mathrm{SDP}_\infty$ as the $r\to\infty$ endpoint and when it compares bounds across ranks; the *strict* form ($K(r,G)$ decreasing, not merely non-increasing) is what makes "the bound at rank $r$" meaningful.
--
--   **Formalization Note** Both sides are `sSup` of the objective over unit families, so the proof is monotonicity of `sSup` over an inclusion of feasible sets. A supporting lemma, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — p. 78 (the rank-constrained problem and the rank-$\infty$ limit).

import Mathlib
import Definitions.Def_Grothendieck_Sdp

open scoped BigOperators Real

namespace Grothendieck

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`SDP_r(G,A)` is monotone in the rank.** For `1 ≤ r ≤ r'`, `sdpRank r G A ≤ sdpRank r' G A`: every
unit family into `ℝ^r` embeds isometrically into `ℝ^{r'}` by padding with zeros. -/
theorem sdpRank_mono {r r' : ℕ} (hr : 1 ≤ r) (hrr' : r ≤ r') (G : SimpleGraph V)
    (A : V → V → ℝ) (hA : ∀ u v, A u v = A v u) :
    sdpRank r G A hA ≤ sdpRank r' G A hA := by sorry

end Grothendieck
