-- Prove2me | Theorems.Thm_LovaszSchrijver_Defect_valid_N_of_deletion_contraction
-- name    : LovaszSchrijver.Defect.valid_N_of_deletion_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:55:33.432707+00:00
-- url     : https://prove2.me/theorems/bb9488d8-a52d-4e66-8b25-a98e46c40eb2
-- title:
--   Lemma 2.2 — valid deletion and contraction of one node give validity for N(K)
-- statement:
--   Let $G = (V,E)$ be a finite graph with no isolated nodes. The paper states this lemma for "any convex body $K$ containing $\mathrm{STAB}(G)$ and contained in $\mathrm{FRAC}(G)$" (p. 177); it is stated here for the homogenized body. Let $K \subseteq \mathbb R^{V\cup\{0\}}$ be a closed convex cone with $K \subseteq \mathrm{FR}(G)$, and say that an inequality $a^{\mathsf T}x \le b$ on $\mathbb R^V$ is valid for $K$ if it holds for every $x \in \mathbb R^V$ with $\binom1x \in K$, and valid for $N(K)$ if it holds for every $x$ with $\binom1x \in N(K)$.
--
--   If $a^{\mathsf T}x \le b$ is an inequality such that for some $v \in V$ both the deletion and the contraction of $v$ give an inequality valid for $K$, then $a^{\mathsf T}x \le b$ is valid for $N(K)$:
--   $$a_{V-v}^{\mathsf T}x \le b \ \text{ and } \ a_{V-\Gamma(v)-v}^{\mathsf T}x \le b - a_v \text{ valid for } K \ \Longrightarrow\ a^{\mathsf T}x \le b \text{ valid for } N(K).$$
--
--   Applied to $K = N^{t}(\mathrm{FR}(G))$, it passes validity from $N^t(G)$ to $N^{t+1}(G)$; this is how the induction in Theorem 2.13 climbs one level at a time.
--
--   **Formalization Note** The body $K$ is taken in homogenized (cone) form so that it applies to $N^{t}(\mathrm{FR}(G))$. The hypothesis "containing $\mathrm{STAB}(G)$" is dropped (the lemma is stronger without it). $K$ is assumed closed: the paper tacitly takes $K$ closed (polyhedral in all its applications), and Lemma 1.3, from which this lemma follows, needs it. Deletion and contraction are the zero-extended coefficient vectors on the same graph. $a$ is an arbitrary real vector.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 178, Lemma 2.2 (with the preamble on p. 177, Section 2.b)

import Mathlib
import Definitions.Def_LovaszSchrijver_Defect_Index

namespace LovaszSchrijver.Defect

theorem valid_N_of_deletion_contraction {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (K : Set (Option V → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K) (hKFR : K ⊆ FR G)
    (a : V → ℝ) (b : ℝ) (v : V)
    (hdel : Valid {x | hom x ∈ K} (deletion a v) b)
    (hcon : Valid {x | hom x ∈ K} (contraction G a v) (b - a v)) :
    Valid {x | hom x ∈ N1 K} a b := by sorry

end LovaszSchrijver.Defect
