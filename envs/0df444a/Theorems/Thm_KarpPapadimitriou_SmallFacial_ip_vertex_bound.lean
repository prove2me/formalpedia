-- Prove2me | Theorems.Thm_KarpPapadimitriou_SmallFacial_ip_vertex_bound
-- name    : KarpPapadimitriou.SmallFacial.ip_vertex_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:40:37.363426+00:00
-- url     : https://prove2.me/theorems/fede61f5-80d6-4b09-b326-97b382979144
-- title:
--   Polynomial binary-size bound for vertices of integer hulls
-- statement:
--   Let $A$ be any integral $m\times n$ matrix and $b$ any integral $m$-vector. Let $s(A,b)$ be the total binary coefficient size, summed over every entry of $A$ and $b$. There is one natural number $k$, independent of $m,n,A,b$, such that every vertex $v$ of the integer hull of $\{x\in\mathbb Q^n:Ax\le b\}$ has integral coordinates and
--   $$|v_i|\le 2^{s(A,b)^k+k}\qquad (1\le i\le n).$$
--   This is the external vertex-size result that the paper invokes in its proof of Lemma 1, attributing it to Borosh–Treybig, Sieveking, S. A. Cook, and Kannan–Monma.
--
--   **Formalization Note** The paper writes “of absolute value $2^{q(s)}$,” read here as “at most.” It omits $x\ge0$ in this cited statement; the Lean version likewise allows all integral points of $Ax\le b$. The integer hull is the published rational definition from Cook–Gerards–Schrijver–Tardos. A zero column creates a line direction in the hull, so it cannot yield a vertex that would violate a bound in $s$ alone.
-- source:
--   Karp & Papadimitriou, MIT/LCS/TM-154 (Feb. 1980), p. 6, proof of Lemma 1, cited vertex bound [2], [13]; https://dspace.mit.edu/server/api/core/bitstreams/eb122126-c312-4445-a8d2-153e3e7d285f/content

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

namespace KarpPapadimitriou.SmallFacial

/-- p. 6, proof of Lemma 1: the cited uniform bound on integer-hull vertices. -/
theorem ip_vertex_bound :
    ∃ k : ℕ, ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
      (v : Fin n → ℚ),
      IsVertex (CookSensitivity.ChvatalRank.integerHull
        (CookSensitivity.ChvatalRank.polyhedron A (fun i => (b i : ℚ)))) v →
      ∀ i, ∃ a : ℤ, v i = (a : ℚ) ∧
        a.natAbs ≤ 2 ^ ((inputSize A b) ^ k + k) := by sorry

end KarpPapadimitriou.SmallFacial
