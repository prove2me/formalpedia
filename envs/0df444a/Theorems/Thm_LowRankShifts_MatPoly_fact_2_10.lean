-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_fact_2_10
-- name    : LowRankShifts.MatPoly.fact_2_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T18:56:30.203008+00:00
-- url     : https://prove2.me/theorems/80fb22b6-8c0c-4f1a-9c41-97565756b738
-- title:
--   Fact 2.10 — the (d+1)-th alternating difference of a polynomial of degree at most d vanishes
-- statement:
--   Let $F$ be any field, $f\in F[x_1,\dots,x_\ell]$ a commutative polynomial of total degree at most $d$, and $x,a_1,\dots,a_{d+1}\in F^\ell$. Then
--
--   $$\sum_{S\subseteq[d+1]}(-1)^{|S|}\,f\Big(x+\sum_{i\in S}a_i\Big)=0 .$$
--
--   This identity is what makes a low-degree function locally correctable: the value at $x$ is a signed sum of the values at the $2^{d+1}-1$ points $x+\sum_{i\in S}a_i$, $S\ne\emptyset$. Lemma 2.11 and Corollary 2.12 rest on it.
--
--   **Formalization Note.** $f$ is an `MvPolynomial (Fin ℓ) F` with `totalDegree ≤ d`; $[d+1]$ is `Fin (d + 1)`.
--
--   Differences from the source:
--   - encoding: [d+1] = {1, …, d+1} and S ⊆ [d+1] → `Fin (d + 1)` and `S : Finset (Fin (d + 1))`; reason: 0-based indices; the same sum
--   - encoding: f ∈ F[x_1, …, x_ℓ] with degree at most d → `f : MvPolynomial (Fin ℓ) F` with `f.totalDegree ≤ d`; reason: Mathlib's multivariate polynomials; the same objects
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 13 (PDF 16), Fact 2.10

import Mathlib

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Fact 2.10 (p. 13): for any field `F`, any commutative polynomial `f ∈ F[x_1, …, x_ℓ]` of total
degree at most `d`, and any `x, a_1, …, a_{d+1} ∈ F^ℓ`,
`Σ_{S ⊆ [d+1]} (−1)^{|S|} f(x + Σ_{i∈S} a_i) = 0`. -/
theorem fact_2_10 {F : Type*} [Field F] {ℓ d : ℕ} (f : MvPolynomial (Fin ℓ) F)
    (hf : f.totalDegree ≤ d) (x : Fin ℓ → F) (a : Fin (d + 1) → Fin ℓ → F) :
    ∑ S : Finset (Fin (d + 1)),
      (-1 : F) ^ S.card * MvPolynomial.eval (x + ∑ i ∈ S, a i) f = 0 := by sorry

end LowRankShifts.MatPoly
