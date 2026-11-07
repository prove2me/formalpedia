-- Prove2me | Theorems.Thm_MatrixSpencer_eq_2_8
-- name    : MatrixSpencer.eq_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:33.720337+00:00
-- url     : https://prove2.me/theorems/e3ba7a8f-6ba5-45a0-a560-25fbd5ecb4b4
-- title:
--   Eq. (2.8), p.9 — lower bound on the diagonal partition function $Z_0$
-- statement:
--   Assume (2.2), and let $M_1,\dots,M_n$ be symmetric with $\sum_iM_i^2\preceq\eta I$. For the partition function $Z_0=\mathbb E_{\gamma_n}e^{-V(B_{\mathrm d})}$ of the diagonal part of the series, $F(0)=\log Z_0$ satisfies
--
--   $$F(0)\ge-\frac43\beta d\eta-\frac{4\alpha d}{3p}(2p\eta)^p-4d\exp\Bigl(-\frac1{8\eta}\Bigr),$$
--
--   stated in exponential form.
--
--   This is the first step of the comparison along the interpolation: the diagonal part is a scalar Gaussian quantity.
--
--   Differences from the source:
--   - reading: M₁,…,Mₙ ∈ ℝ^{d×d} (no word "symmetric") → the Mᵢ are symmetric; reason: ⪯ and V(X) = Tr v(X) are defined for symmetric matrices only (p.6, p.8), and the only use of the statement has symmetric Mᵢ
--   - encoding: −log Z₀ ≤ (4/3)βdη + (4αd/(3p))(2pη)^p + 4d e^{−1/(8η)} → exp(−((4/3)βdη + (4αd/(3p))(2pη)^p + 4d e^{−1/(8η)})) ≤ Z₀; reason: Lean's log 0 = 0 would make the printed form silently true at zero partition function; the two forms agree for a positive partition function
--   - encoding: q and r_q in Step 1–3 and Appendix C → p and r_p; reason: the same integer; the page uses both letters
--   - encoding: V = +∞ outside the unit ball → the real weight e^{−V} is 0 there; reason: the value +∞ is never computed with
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, Step 1, (2.8), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_MatrixSpencer_Param22
import Definitions.Def_MatrixSpencer_partition

namespace MatrixSpencer

/-- **Lower bound (2.8) on the diagonal partition function, proof of Theorem 2.5, Step 1.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), proof of Theorem 2.5, Step 1, (2.8), p.9 (PDF p.11): "F(0) ≥ −(4/3)βdη − (4αd/(3q))(2qη)^q −
4d exp(−1/(8η)). (2.8)"

**Formalization Note.** `F(0) = log Z₀`. The page writes `q` for `p` from (2.6) on; it is the same
integer. The bound is stated as `e^{−E} ≤ Z₀`, as in `theorem_2_5`. -/
theorem eq_2_8 {n d : ℕ} (α β : ℝ) (p : ℕ) (η : ℝ) (h : Param22 α β p η)
    (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef) :
    Real.exp (-(4 / 3) * β * d * η - (4 * α * d / (3 * p)) * (2 * p * η) ^ p -
        4 * d * Real.exp (-1 / (8 * η))) ≤
      partition α β p M 0 := by sorry

end MatrixSpencer
