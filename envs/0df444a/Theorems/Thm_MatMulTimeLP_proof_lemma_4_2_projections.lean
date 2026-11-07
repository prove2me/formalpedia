-- Prove2me | Theorems.Thm_MatMulTimeLP_proof_lemma_4_2_projections
-- name    : MatMulTimeLP.proof_lemma_4_2_projections
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:48:41.040971+00:00
-- url     : https://prove2.me/theorems/ba07922e-2116-4ea3-889e-70b40768f553
-- title:
--   Proof of Lemma 4.2, last sentence — the projections take $O((d+n)^{\omega+o(1)})$ machine steps
-- statement:
--   There is a family of real-RAM programs, one for each size $(d,n)$, a function $g$ with $g(m)\to 0$ and a constant $C>0$ such that, for all $d$, $n\ge 1$, all $A\in\mathbb R^{d\times n}$ and all $x>0$: on every tape, the program reading $A$ and $x$ halts within
--
--   $$C\,(d+n)^{\omega+g(d+n)}$$
--
--   steps and outputs the orthogonal projection $P$ onto $\mathrm{im}(XA^\top)$ and a matrix $L\in\mathbb R^{d\times n}$ with $(XA^\top)L=P$.
--
--   This is the only place where $\omega$ enters the algorithm: $P$ gives $H$ and $h$, and $\lambda=L(\sigma'-x\circ s/\tau')$ gives $y^+$ with no further inversion.
--
--   **Formalization Note** $\omega$ is `OAI.MatrixMultiplication.Arithmetic.omega ℝ`. There is no rank hypothesis, because Lemma 4.2 has none, and $d>n$ is allowed.
--
--   Differences from the source:
--   - reading: $O((d+n)^{\omega+o(1)})$ time → one family of programs, one $g\to 0$ and one $C$, chosen before the instance; reason: the published $\omega$ is non-uniform, one straight-line program per size, and that is what allows a single $o(1)$
--   - reading: "computing and applying the projections" → computes $P$ and $L$, on every tape; reason: the page's work is deterministic; applying $P$ or $L$ to a vector is a matrix-vector product within the same bound, and is not stated
--   - encoding: exact real arithmetic with unit-cost operations → the deep randomized real RAM, every instruction costing $1$; reason: Section 3, p.15; a Lean function under `∃` would compute the answer for free
--   - generalization: the setting of Lemma 4.2, $n\ge 100$, $x>0$ → every $n\ge 1$ and every $x>0$, with any $d$; reason: the page's instances are among these; $n=0$ is excluded only because $0^{\omega+g}=0$ would make any step bound false at $d=0$
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Proof of Lemma 4.2, last sentence, p.21; bullet, p.4

import Mathlib
import Definitions.Def_MatMulTimeLP_LP
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

namespace MatMulTimeLP

open Matrix Filter Topology

/-- Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), proof of Lemma 4.2, last sentence, p.21: the projections can
be computed in `O((d+n)^(ω+o(1)))` time. A per-size family of programs on the real RAM reads `A` and `x > 0`,
halts on every tape within `C (d+n)^(ω+g(d+n))` steps, and outputs the orthogonal projection `P` onto
`im(XAᵀ)`, and a `d × n` matrix `L` with `(XAᵀ)L = P`. Then `λ = L(σ' - Xs/τ')` gives `y⁺` of Lemma 4.2, and `P`
gives `H`, `h`.

**Formalization Note** No rank hypothesis, as Lemma 4.2 has none, and `d > n` is allowed, hence `d + n`. The bound
holds on every tape: the page's work is deterministic. `ω` is the published non-uniform exponent, which is why the
program depends on the size. Output: `P` row by row, then `L` row by row. -/
theorem proof_lemma_4_2_projections :
    ∃ (alg : ℕ → ℕ → Program) (g : ℕ → ℝ) (C : ℝ), Tendsto g atTop (𝓝 0) ∧ 0 < C ∧
      ∀ (d n : ℕ), 1 ≤ n → ∀ (A : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ), (∀ j, 0 < x j) →
        ∀ ω : Tape, ∃ t : ℕ, HaltsAt (alg d n) (projInput A x) ω t ∧
          ((t + 1 : ℕ) : ℝ) ≤
            C * ((d : ℝ) + n) ^ (OAI.MatrixMultiplication.Arithmetic.omega ℝ + g (d + n)) ∧
          IsOrthoProjOnto (outputMatAt (alg d n) (projInput A x) ω t 0 n n) (diagonal x * Aᵀ) ∧
          (diagonal x * Aᵀ) * outputMatAt (alg d n) (projInput A x) ω t (n * n) d n =
            outputMatAt (alg d n) (projInput A x) ω t 0 n n := by sorry

end MatMulTimeLP
