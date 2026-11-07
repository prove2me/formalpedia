-- Prove2me | Theorems.Thm_MatchVec3_exact_weight_polynomial
-- name    : MatchVec3.exact_weight_polynomial
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:40:54.918815+00:00
-- url     : https://prove2.me/theorems/3812fd3c-8e49-4de6-9e3c-cbfaa6b1e2dc
-- title:
--   Proof of Theorem 5.2: exact-weight polynomial in the elementary symmetric basis
-- statement:
--   Let $p$ be a prime and $0\le r\le L$. There are coefficients $c_d\in\mathbb F_p$ such that
--
--   $$P_r(z_1,\dots,z_L)=\sum_{d=0}^L c_d\,e_d(z)\in\mathbb F_p[z_1,\dots,z_L]$$
--
--   has degree at most $L$, equals $1$ on Boolean inputs of Hamming weight $r$, and equals $0$ on Boolean inputs of every other Hamming weight. Here $e_d$ is the elementary symmetric polynomial of degree $d$.
--
--   It converts the exact count of $\beta$-residues into a polynomial of the indicator values.
--
--   Differences from the source:
--   - generalization: F_p with p from m = p^a q^b, and L > q → any prime p and any L; reason: the triangular argument uses neither
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.15

import Mathlib

namespace MatchVec3

/-- **The exact-weight polynomial** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), proof of Theorem 5.2, p.15): for every `r ∈ {0, …, L}` there is a polynomial
`P_r(z_1, …, z_L) = ∑_{d=0}^L c_{r,d} e_d(z)` over `F_p`, of degree at most `L`, that equals `1` on
Boolean inputs of Hamming weight `r` and `0` on Boolean inputs of every other Hamming weight. -/
theorem exact_weight_polynomial {p : ℕ} (hp : p.Prime) (L r : ℕ) (hr : r ≤ L) :
    ∃ (c : ℕ → ZMod p) (P : MvPolynomial (Fin L) (ZMod p)),
      P = ∑ d ∈ Finset.range (L + 1), MvPolynomial.C (c d) * MvPolynomial.esymm (Fin L) (ZMod p) d ∧
      P.totalDegree ≤ L ∧
      ∀ z : Fin L → ZMod p, (∀ s, z s = 0 ∨ z s = 1) →
        MvPolynomial.eval z P = if (Finset.univ.filter fun s => z s = 1).card = r then 1 else 0 := by sorry

end MatchVec3
