-- Prove2me | Theorems.Thm_LovaszSchrijver_OddHole_valid_N_of_deletion_contraction
-- name    : LovaszSchrijver.OddHole.valid_N_of_deletion_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:47:39.57484+00:00
-- url     : https://prove2.me/theorems/d8015190-5569-482b-bbed-859de50a9981
-- title:
--   Lemma 2.2 — deletion and contraction valid for K imply validity for N(K)
-- statement:
--   Let $G = (V, E)$ be a finite graph with no isolated nodes, and let $K \subseteq \mathrm{FR}(G)$ be a closed convex cone in $\mathbb{R}^{V \cup \{0\}}$. Write $K|_{x_0=1} = \{x \in \mathbb{R}^V : (1, x) \in K\}$, and similarly $N(K)|_{x_0 = 1}$. Let $a \in \mathbb{R}^V$, $b \in \mathbb{R}$ and $v \in V$. If
--
--   1. the deletion $a_{V-v}^{\mathsf T} x \le b$ of $v$ is valid for $K|_{x_0=1}$, and
--   2. the contraction $a_{V-\Gamma(v)-v}^{\mathsf T} x \le b - a_v$ of $v$ is valid for $K|_{x_0=1}$,
--
--   then
--   $$\sum_{i \in V} a_i x_i \le b \quad \text{for every } x \in N(K)|_{x_0=1}.$$
--
--   In the paper (p. 177) $K$ is "any convex body containing $\mathrm{STAB}(G)$ and contained in $\mathrm{FRAC}(G)$". The lemma reduces validity after one round of $N$ to validity of two smaller inequalities before it; it is how the odd hole constraints are shown to hold for $N(G)$.
--
--   **Formalization Note** The lemma is stated in cone form: $K$ is a closed convex cone inside $\mathrm{FR}(G)$, and validity is read on the slice $x_0 = 1$. The paper's convex body corresponds to the cone it spans, which is closed and lies in $\mathrm{FR}(G)$. The hypothesis $\mathrm{STAB}(G) \subseteq K$ is dropped; dropping it strengthens the statement. Deletion and contraction are coefficient vectors on the same graph $G$ (coefficients set to $0$) rather than inequalities on the subgraphs $G - v$ and $G - \Gamma(v) - v$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, Lemma 2.2 (with the preamble on p. 177, Section 2.b)

import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones
import Definitions.Def_LovaszSchrijver_OddHole_DeletionContraction

namespace LovaszSchrijver.OddHole

/-- Lemma 2.2 (p. 178), cone form: let `K ⊆ FR(G)` be a closed convex cone. If for some
node `v` both the deletion and the contraction of `v` give inequalities valid for `K`
(read on the slice `x₀ = 1`), then `aᵀx ≤ b` is valid for `N(K)` (read on `x₀ = 1`). -/
theorem valid_N_of_deletion_contraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N K} a b := by sorry

end LovaszSchrijver.OddHole
