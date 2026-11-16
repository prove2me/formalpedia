-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_theorem_4_1
-- name    : LatticeAvgPrec.OneVector.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:42:31.067577+00:00
-- url     : https://prove2.me/theorems/44d324dc-b764-4972-87a6-ff632d32cebd
-- title:
--   Theorem 4.1 — A complete basis at average precision
-- statement:
--   Fix $2<\omega\le3$ available. There are a program $\mathcal P$ of the logarithmic-cost RAM with coin flips, a constant $c>0$ and a subpolynomial factor $g$ such that:
--
--   1. for every $n\ge1$ and every $H\in\mathbb Z^{n\times n}$ in upper column HNF, with $\mathcal D=\log_2\det H$, on input $H$ the program is Las Vegas, outputs an integer basis $Z$ with
--
--   $$
--   Z\mathbb Z^n=\Lambda(H),\qquad \|Z_i\|_2\le 2^{cn}\,\lambda_i(\Lambda(H))\quad(1\le i\le n),
--   $$
--
--   and runs in expected $g(n,\lceil\mathcal D\rceil)\,n^{\omega-1}(\mathcal D+n^2)$ bit operations, input and output included;
--   2. for every $n\ge1$ and every nonsingular $B\in\mathbb Z^{n\times n}$ of total row bitlength $L$, on input $B$ the program is Las Vegas, outputs an integer basis $Z$ of $\Lambda(B)$ with $\|Z_i\|_2\le 2^{cn}\lambda_i(\Lambda(B))$ for all $i$, and runs in expected $g(n,L)\,n^{\omega-1}(L+n^2)$ bit operations.
--
--   The informal Theorem 1.2 (p.4) is part 2: $n^{\omega}(L/n+n)=n^{\omega-1}(L+n^2)$. The theorem extends the one-vector result of the mission's goal to a complete basis with indexed successive-minima guarantees, at the cost of matrix multiplication at precision $L/n+n$; Theorem 5.1 shows this is near-optimal relative to integer matrix multiplication.
--
--   **Formalization Note** One program, one constant $c$ of $2^{O(n)}$ and one factor $g$ serve both parts; $\widetilde O$ follows the conventions of §1.1.1 (p.4), as in the published goal: $\widetilde O$ suppresses a subpolynomial factor in the dimension and precision parameters, chosen with the program after $\omega$ and before every input. Columns are indexed from $0$, so column $i$ is compared with $\lambda_{i+1}$. "Including preprocessing and output" is the cost of the whole run from the code of the input to the code of $Z$.
--
--   Differences from the source:
--   - reading: "The construction in this section computes …"; "It makes O(log n) reduction calls on geometrically decreasing ranks." → ∃ program with the output and cost guarantees; the number of reduction calls is not encoded; reason: the sentence describes the construction of §4, not a property of the output or the cost (the published goal treats "at most one approximate-SVP call" the same way)
--   - reading: 2^{O(n)} and Õ(n^{ω−1}(𝓓+n²)), Õ(n^{ω−1}(L+n²)) → one constant c and one subpolynomial g(n, ⌈𝓓⌉) or g(n, L), chosen after ω and before the input; reason: the conventions of §1.1.1, as in the published goal
--   - encoding: H in upper column HNF, 𝓓 = log det H → IsHNF H, 𝓓 = log₂ det H; reason: the published HNF shape; det H > 0 follows from it
--   - encoding: Z_i, λ_i for 1 ≤ i ≤ n → column i ∈ Fin n against lam (lat H) (i+1); reason: Lean indexes columns from 0
--   - reading: one construction with integer preprocessing for "a general integer input" → one program P for both the HNF input and every nonsingular B, with n ≥ 1; reason: the theorem describes a single construction (preprocessing included), Theorem 1.2 states the general input nonsingular, and for HNF input L ≤ 𝓓 + 3n, so the general bound already implies the HNF bound
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 4.1, p.13 (informal Theorem 1.2, p.4; proof pp.19–20)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Theorem 4.1** (A complete basis at average precision; STOC 2027 submission #1574, p.13;
informal form Theorem 1.2, p.4). Let `H ∈ ℤ^{n×n}` be in upper column HNF and `𝓓 = log det H`. One
computes an integer basis `Z` with `Zℤ^n = Λ(H)` and `‖Z_i‖₂ ≤ 2^{O(n)} λ_i(Λ(H))` in expected
`Õ(n^{ω−1}(𝓓 + n²))` bit operations, including preprocessing and output. For a general integer input
of total row bitlength `L`, the bound including integer preprocessing is `Õ(n^{ω−1}(L + n²))`.

**Formalization Note** One program `P`, one constant `c` of `2^{O(n)}` and one subpolynomial factor
`g` serve both inputs; they are chosen after `ω` and before the input. Columns are indexed from `0`,
so column `i` is compared with `λ_{i+1}`. Theorem 1.2's `Õ(n^ω(L/n + n))` is the same bound. -/
theorem theorem_4_1 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (P : TimeSpaceMA.Program) (c : ℝ) (g : ℕ → ℕ → ℝ), 0 < c ∧ IsSubpoly g ∧
      (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → IsHNF H →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode H))
          (fun mem => ∃ Z : Matrix (Fin n) (Fin n) ℤ, memHolds mem (matCode Z) ∧
            lat Z = lat H ∧
            ∀ i : Fin n, colNorm Z i ≤ (2 : ℝ) ^ (c * n) * lam (lat H) ((i : ℕ) + 1))
          (g n ⌈Real.logb 2 (H.det : ℝ)⌉₊ * (n : ℝ) ^ (ω - 1) *
            (Real.logb 2 (H.det : ℝ) + (n : ℝ) ^ 2))) ∧
      (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → B.det ≠ 0 →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf (matCode B))
          (fun mem => ∃ Z : Matrix (Fin n) (Fin n) ℤ, memHolds mem (matCode Z) ∧
            lat Z = lat B ∧
            ∀ i : Fin n, colNorm Z i ≤ (2 : ℝ) ^ (c * n) * lam (lat B) ((i : ℕ) + 1))
          (g n (totalRowBits B) * (n : ℝ) ^ (ω - 1) *
            ((totalRowBits B : ℝ) + (n : ℝ) ^ 2))) := by sorry

end LatticeAvgPrec.OneVector.Supplement
