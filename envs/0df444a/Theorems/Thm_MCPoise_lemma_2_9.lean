-- Prove2me | Theorems.Thm_MCPoise_lemma_2_9
-- name    : MCPoise.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:40.435037+00:00
-- url     : https://prove2.me/theorems/c341f262-dd20-4bae-bc57-3ebd098a3e1d
-- title:
--   Lemma 2.9 and the count of $S'_j$ — at most $|S_j|C/4$ long paths and $|S_j| \le 3|S'_j|$
-- statement:
--   Let $(\hat x, \hat f)$ be feasible for Multiroot-LP, and take the data of Stage 1 for a nonempty group $j$: normalized $\hat x$, the integer $C$, the multigraph, a packing and the selected sets $Q^t_j$.
--
--   **Lemma 2.9.** The number of paths of the packing of length greater than $4L'_d$ is at most $|S_j|C/4$. In consequence, at least $|S_j|/3$ terminals satisfy $\sum_{p \in Q^t_j} y^{j,t}_p \ge 1$.
--
--   This item states the Lemma and the count that the page derives right after it.
--
--   Differences from the source:
--   - generalization: the packing of size ½Σλ from Theorem 2.8 → any S⁺_j-path-packing with such selections; reason: the proof does not read the size of the packing
--   - encoding: parameter L′_d → a natural number; reason: it bounds a number of edges, and the only L′_d the paper uses is the integer ρ²L_d
--   - generalization: the discarded paths (selected paths of length greater than 4L′_d removed from the collections Q^t_j) → every path of the packing Q_j of length greater than 4L′_d; reason: the discarded paths are among them, so the bound on the larger count implies the page's, and the proof (edge-disjointness and the edge count of the multigraph) bounds the larger count
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.9 and the following display, p.18

import Mathlib
import Definitions.Def_MCPoise_MultirootLP
import Definitions.Def_MCPoise_IsStage1

namespace MCPoise

/-- **Lemma 2.9 and the count of `S′_j`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.9, p.18: "The number of discarded paths is at most |S_j|C/4." And after it: "there must be at least |S_j|/3 terminals for which
Σ_{p∈Q^t_j} y^{j,t}_p ≥ 1."

For a feasible Multiroot-LP solution whose `x̂` is normalized, and the data of Stage 1 for a nonempty group `j`: at most `|S_j|C/4` packed paths have length greater
than `4L′_d`, and `|S_j| ≤ 3|S′_j|`.

**Formalization Note.** Both claims are in one item since the second is the page's use of the first. The first counts each path of the packing once ("each
discarded path in the packing is counted once"). -/
theorem lemma_2_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) {μ : ℕ} (r : Fin μ → V)
    (S : Fin μ → Finset V) (LΔ : ℝ) (Lp : ℕ) (x : Sym2 V → Fin μ → ℝ) (f : Fin μ → V → List V → ℝ)
    (hLP : MultirootLP G r S LΔ Lp x f) (j : Fin μ) (C : ℕ) (M : MGraph V) (Q : List (MPath V))
    (Qt : V → Finset (Fin Q.length))
    (hst : IsStage1 G (r j) (S j) Lp (f j) (fun e => x e j) C M Q Qt) :
    (Q.filter fun p => 4 * Lp < p.es.length).length * 4 ≤ (S j).card * C ∧
      (S j).card ≤ 3 * (Sprime (S j) Lp C Q Qt).card := by sorry

end MCPoise
