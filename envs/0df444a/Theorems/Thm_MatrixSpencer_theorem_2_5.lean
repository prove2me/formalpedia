-- Prove2me | Theorems.Thm_MatrixSpencer_theorem_2_5
-- name    : MatrixSpencer.theorem_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:23.965319+00:00
-- url     : https://prove2.me/theorems/1749f10f-2b5d-47ab-bd4a-9f9a88f86e9c
-- title:
--   Theorem 2.5, p.8 — partition function lower bound from interpolation
-- statement:
--   Assume (2.2) with $p\ge2$. Let $M_1,\dots,M_n\in\mathbb R^{d\times d}$ be symmetric with $\sum_iM_i^2\preceq\eta I$, and let $B=\sum_ig_iM_i$. Let $Z_1=\mathbb E_{\gamma_n}e^{-V(B)}$ be the partition function of the potential $V$ at the full series. Then
--
--   $$-\log Z_1\le 12\beta d\eta+7\alpha d(2p\eta)^p+4de^{-1/(8\eta)},$$
--
--   stated in the form $\exp(-\mathrm{RHS})\le Z_1$.
--
--   Since $e^{-V}\le\mathbf 1_{\{\|B\|<1\}}$, this lower bound is what gives the small-ball estimate of Theorem 1.4.
--
--   **Formalization Note** At $\eta=0$ all $M_i$ vanish, $Z_1=1$, and Lean's $1/0=0$ only enlarges the right side.
--
--   Differences from the source:
--   - reading: M₁,…,Mₙ ∈ ℝ^{d×d} (no word "symmetric") → the Mᵢ are symmetric; reason: ⪯ and V(X) = Tr v(X) are defined for symmetric matrices only (p.6, p.8), and the only use of the statement has symmetric Mᵢ
--   - encoding: −log Z₁ ≤ 12βdη + 7αd(2pη)^p + 4de^{−1/(8η)} → exp(−(12βdη + 7αd(2pη)^p + 4de^{−1/(8η)})) ≤ Z₁; reason: Lean's log 0 = 0 would make the printed form silently true at zero partition function; the two forms agree for a positive partition function
--   - encoding: V = +∞ outside the unit ball → the real weight e^{−V} is 0 there; reason: the value +∞ is never computed with
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MatrixSpencer_Param22
import Definitions.Def_MatrixSpencer_partition

namespace MatrixSpencer

/-- **Theorem 2.5 (Partition function lower bound from interpolation).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem 2.5, p.8 (PDF p.10): "Assume that (2.2) holds. Let M₁, …, Mₙ ∈ ℝ^{d×d} satisfy ∑ⁿᵢ₌₁ Mᵢ² ⪯ ηI.
Let B = ∑ⁿᵢ₌₁ gᵢMᵢ, and for 0 ≤ t ≤ 1 denote with B_t(g) = B_d(g) + tY(g) the interpolation between
diagonal and off diagonal part of the matrix series B. Moreover, let Z_t = E_{γₙ}e^{−V(B_t)} be the
partition function associated with the potential V. Then, −log Z₁ ≤ 12βdη + 7αd(2pη)^p + 4de^{−1/(8η)}.
(2.3)"

**Formalization Note.** The `Mᵢ` are symmetric: the page's `⪯` and `V(X) = Tr v(X)` are defined for
symmetric matrices only (p.6), and the only use has symmetric `Mᵢ`. The bound is stated as
`e^{−E} ≤ Z₁`, because Lean's `log 0 = 0` would make the printed form silently true at `Z₁ = 0`. At
`η = 0` all `Mᵢ` vanish and `Z₁ = 1`, while Lean's `1/0 = 0` only enlarges the right side of (2.3). -/
theorem theorem_2_5 {n d : ℕ} (α β : ℝ) (p : ℕ) (η : ℝ) (h : Param22 α β p η)
    (M : Fin n → Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i, (M i).IsSymm)
    (hV : (η • (1 : Matrix (Fin d) (Fin d) ℝ) - ∑ i, M i ^ 2).PosSemidef) :
    Real.exp (-(12 * β * d * η + 7 * α * d * (2 * p * η) ^ p +
        4 * d * Real.exp (-1 / (8 * η)))) ≤
      partition α β p M 1 := by sorry

end MatrixSpencer
