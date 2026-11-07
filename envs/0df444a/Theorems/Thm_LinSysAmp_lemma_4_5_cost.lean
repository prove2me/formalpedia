-- Prove2me | Theorems.Thm_LinSysAmp_lemma_4_5_cost
-- name    : LinSysAmp.lemma_4_5_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:57:47.188197+00:00
-- url     : https://prove2.me/theorems/de3d2923-c009-47a9-bf0b-cbe1d04d6bff
-- title:
--   Lemma 4.5, item 1 (cost) — $RM$ in $O(n^2k^{\omega-2+o(1)})$ operations
-- statement:
--   Let $F$ be a finite field and let $\omega$ be the exponent of matrix multiplication over $F$. For every $\varepsilon>0$ there is a constant $C>0$ such that for all $1\le k\le n$ there is a straight-line arithmetic program over $F$ that takes the entries of $M\in F^{n\times n}$ and $U,V\in F^{n\times k}$ as inputs, computes every entry of $(I_n+UV^\top)M$, is correct on all inputs, and has cost
--   $$
--   \text{cost}\le C\,n^2\,k^{\omega-2+\varepsilon}.
--   $$
--
--   This is the statement that one low-rank update costs far less than a general matrix product, which is what makes the amplification cheap.
--
--   **Formalization Note** The model is the straight-line model of the definition of $\omega$: constants and inputs are free, and each $+,-,\times$ gate costs $1$. Correctness is required on all matrices over $F$, which is all that "computing $RM$" asks.
--
--   Differences from the source:
--   - reading: computing RM takes O(n²k^{ω−2+o(1)}) operations → ∀ε>0 ∃C ∀n,k, a straight-line program correct for all M, U, V with cost ≤ C·n²·k^{ω−2+ε}; reason: the o(1) of a statement about ω, which is an infimum and need not be attained; the page's proof counts arithmetic operations of block multiplication
--   - reading: ω, "the exponent of matrix multiplication over the field under consideration" (§3.2) → `omegaAlg F`, whose programs compute the product as polynomials; reason: the standard algebraic exponent; see the item `LinSysAmp.omegaAlg`
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Lemma 4.5, item 1, second sentence, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_LinSysAmp_omegaAlg

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-- Lemma 4.5, item 1, second sentence (p.19, PDF p.21). Couteau, Melissaris, Radhika Sajith,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Given M, computing RM takes O(n²k^{ω−2+o(1)}) operations." (R = I_n + UV⊤ with U, V ∈ F^{n×k}.)

**Formalization Note.** Stated in the straight-line model in which `ω` is defined
(`OAI.MatrixMultiplication.Arithmetic`): constants and inputs are free, each `+, −, ×` gate costs `1`.
`ω` is `omegaAlg F`, the exponent over the same field `F` (§3.2: "the exponent of matrix
multiplication over the field under consideration"). `O(n²k^{ω−2+o(1)})` is
read as: for every `ε > 0` there is one constant `C` (depending on `F` and `ε` only) such that for all
`1 ≤ k ≤ n` some program computes every entry of `(I + UV⊤)M` from the entries of `M, U, V`, correctly
for all inputs, with cost at most `C n² k^{ω−2+ε}`. The inputs are indexed by
`(Fin n × Fin n) ⊕ (Fin n × Fin k) ⊕ (Fin n × Fin k)` (entries of `M`, `U`, `V`). -/
theorem lemma_4_5_cost (F : Type*) [Field F] [Fintype F] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      ∃ (r : ℕ)
        (p : OAI.MatrixMultiplication.Arithmetic.Program F
          ((Fin n × Fin n) ⊕ (Fin n × Fin k) ⊕ (Fin n × Fin k)) r)
        (out : Fin n → Fin n → Fin r),
        (∀ (M : Matrix (Fin n) (Fin n) F) (U V : Matrix (Fin n) (Fin k) F) (i j : Fin n),
          p.eval (Sum.elim (fun a => M a.1 a.2) (Sum.elim (fun b => U b.1 b.2) (fun c => V c.1 c.2)))
              (out i j) = (((1 : Matrix (Fin n) (Fin n) F) + U * Vᵀ) * M) i j) ∧
        (p.cost : ℝ) ≤ C * (n : ℝ) ^ 2 * (k : ℝ) ^ (omegaAlg F - 2 + ε) := by sorry

end LinSysAmp
