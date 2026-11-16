-- Prove2me | Theorems.Thm_LatticeAvgPrec_OneVector_Supplement_theorem_1_4
-- name    : LatticeAvgPrec.OneVector.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:44:45.505854+00:00
-- url     : https://prove2.me/theorems/84af9f7c-c261-4036-a237-106f91d2a937
-- title:
--   Theorem 1.4 (formal form Corollary 6.1) — Polynomial factorization
-- statement:
--   Fix $2<\omega\le3$ available. There are a program $\mathcal A$ of the logarithmic-cost RAM with coin flips and a subpolynomial factor $g$ such that the following holds. Let $P\in\mathbb Z[x]$ be primitive with positive leading coefficient and degree $N\ge2$, and let $\tau=\max_i\mathrm{bits}(P_i)\ge1$ be its coefficient bitlength. On input the coefficient vector of $P$, $\mathcal A$ is Las Vegas and outputs a list $((u_1,e_1),\dots,(u_k,e_k))$ with
--
--   1. the $u_i\in\mathbb Z[x]$ pairwise distinct, primitive, with positive leading coefficient and degree at least $1$, and irreducible in $\mathbb Q[x]$;
--   2. $e_i\ge1$ and
--   $$P=\prod_{i=1}^k u_i^{e_i},$$
--
--   in expected
--
--   $$
--   g(N,\tau)\,N^{\omega}(N+\tau)
--   $$
--
--   bit operations, input and output included (23).
--
--   That is, the complete factorization of $P$ over $\mathbb Q$, with multiplicities, at a cost a factor $N$ below the LLL coefficient search run with direct lattice reduction (Table 2, p.6).
--
--   **Formalization Note** The input is the code of $(P_0,\dots,P_N)$; the output is the code of the list of pairs. For primitive $u_i$ of positive degree, irreducibility over $\mathbb Q$ and over $\mathbb Z$ agree. $\tau\ge1$ holds automatically for the paper's $\mathrm{bits}$. $\widetilde O$ follows the conventions of §1.1.1 (p.4), as in the published goal: $\widetilde O$ suppresses a subpolynomial factor in the dimension and precision parameters, chosen with the program after $\omega$ and before every input.
--
--   Differences from the source:
--   - reading: Theorem 1.4: "a degree-N integer polynomial with coefficient bitlength τ" → the setting of Corollary 6.1 (p.22): P primitive, lc(P) > 0, N ≥ 2, τ ≥ 1; reason: Corollary 6.1 is the paper's formal statement of Theorem 1.4 (Table 2 cites it); its setting sentence states these hypotheses
--   - reading: "completely factors P over ℚ" → a list of pairwise distinct primitive, positive-leading-coefficient factors of degree ≥ 1, irreducible over ℚ, with multiplicities e_i ≥ 1 and P = ∏ u_i^{e_i}; reason: for primitive P with lc > 0 this is the complete factorization over ℚ, normalized in ℤ[x] (the proof records multiplicities, p.23)
--   - reading: "Using the one-vector algorithm of Corollary 3.4, the classical LLL polynomial factorization algorithm …" in expected Õ(N^ω(N+τ)) → ∃ program and subpolynomial g(N, τ) with LasVegasWithin, bound g(N, τ) N^ω (N+τ); reason: the sentence names the algorithm; its output and cost are the formal content, as in the published goal
--   - encoding: P and its factorization → codes of the coefficient vector and of the list of (factor, multiplicity) pairs; reason: binary input and output (§1.1.1)
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), Theorem 1.4, p.6; formal statement Corollary 6.1 with its setting, p.22 (proof pp.23–24)

import Definitions.Def_LatticeAvgPrec_OneVector_Supplement_Objects
open Matrix

namespace LatticeAvgPrec.OneVector.Supplement

/-- **Theorem 1.4** (Polynomial factorization; STOC 2027 submission #1574, p.6; formal form
Corollary 6.1 with its setting, p.22). Let `P ∈ ℤ[x]` be primitive with positive leading
coefficient, degree `N ≥ 2` and coefficient bitlength `τ ≥ 1`. A Las Vegas algorithm completely
factors `P` over `ℚ` in expected bit cost `Õ(N^ω(N + τ))` (23).

**Formalization Note** The input is the code of the coefficient vector `(P_0, …, P_N)`; the output
is the code of a list `((u_1, e_1), …, (u_k, e_k))` of pairwise distinct primitive integer
polynomials with positive leading coefficient and degree `≥ 1`, irreducible over `ℚ`, with
multiplicities `e_i ≥ 1` and `P = ∏ u_i^{e_i}`. `τ = max_i bits(P_i) ≥ 1` holds automatically.
The program and the subpolynomial factor `g(N, τ)` are chosen after `ω` and before the input. -/
theorem theorem_1_4 (ω : ℝ) (hω₁ : 2 < ω) (hω₂ : ω ≤ 3) (hM : MatMulAvailable ω) :
    ∃ (A : TimeSpaceMA.Program) (g : ℕ → ℕ → ℝ), IsSubpoly g ∧
      ∀ P : Polynomial ℤ, P.IsPrimitive → 0 < P.leadingCoeff → 2 ≤ P.natDegree →
        SoftmaxAttnFD.LasVegasWithin A (TimeSpaceMA.memOf (polyCode P))
          (fun mem => ∃ l : List (Polynomial ℤ × ℕ), memHolds mem (factorListCode l) ∧
            (l.map Prod.fst).Nodup ∧
            (∀ u ∈ l, u.1.IsPrimitive ∧ 0 < u.1.leadingCoeff ∧ 1 ≤ u.1.natDegree ∧
              Irreducible (u.1.map (Int.castRingHom ℚ)) ∧ 1 ≤ u.2) ∧
            P = (l.map (fun u => u.1 ^ u.2)).prod)
          (g P.natDegree (coeffBits P) * (P.natDegree : ℝ) ^ ω *
            ((P.natDegree : ℝ) + coeffBits P)) := by sorry

end LatticeAvgPrec.OneVector.Supplement
