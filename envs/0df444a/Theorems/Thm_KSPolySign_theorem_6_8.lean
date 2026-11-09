-- Prove2me | Theorems.Thm_KSPolySign_theorem_6_8
-- name    : KSPolySign.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:37:18.498355+00:00
-- url     : https://prove2.me/theorems/2664dbfa-b21a-4b7d-9830-ba7873ce3003
-- title:
--   Theorem 6.8 — deterministic polynomial-time signing of rank-one Hermitian matrices with constant $3.4814$
-- statement:
--   Let $A_1,\dots,A_m\in\mathbb C^{n\times n}$ be Hermitian matrices of rank at most one.
--
--   1. There are signs $\sigma\in\{\pm1\}^m$ such that
--   $$\Big\|\sum_i\sigma_iA_i\Big\|\le3.4814\,\Big\|\sum_iA_i^2\Big\|^{1/2}.$$
--   2. For rational inputs, a deterministic algorithm (Algorithm 3) finds such signs using $T_{\mathrm{arith}}\le\tilde O(mn^2+n^{56})$ arithmetic operations, where $\tilde O$ suppresses logarithmic factors in $m,n$.
--   3. If $A_i=a_ia_i^*$, $\sum_iA_i=I$ and $\|a_i\|^2\le\alpha$, then for the sign classes $I_1=\{i:\sigma_i=1\}$, $I_2=\{i:\sigma_i=-1\}$,
--   $$\Big\|\sum_{i\in I_j}a_ia_i^*-\tfrac12I\Big\|\le1.7407\sqrt\alpha,\qquad j=1,2.$$
--   For rational $a_ia_i^*$ the partition has the same arithmetic bound.
--
--   This is a polynomial-time algorithm for Weaver's discrepancy form of the Kadison–Singer problem, with constant $3.4814$ (the existence constant of Xie–Xu–Zhu is $3$).
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean operator norm. Part 2 asserts one program of the published real RAM, restricted to rational literals and no square roots or random draws; its arithmetic operations (additions, subtractions, multiplications, divisions, comparisons of reals) are at most $C(mn^2+n^{56})\log(m+n+2)^k$ and its total number of steps at most $C(m+n+2)^k$, with $C,k$ fixed before the input. The input lists the real and imaginary parts of every entry; the signs are the $m$ output cells. Part 3 is stated for every signing meeting the bound of part 1.
--
--   Differences from the source:
--   - reading: Algorithm 3 uses T_arith arithmetic operations (deterministic, rational inputs) → one VecBalPoly.Admissible program (rational literals, no square root, no random draws) on the published real RAM; arithmetic operations = VecBalPoly.realOps (+, −, ×, ÷, comparisons); reason: the paper's arithmetic work counts comparisons (p.82, p.40) and evaluates β by rational bisection without square roots (Lemma 6.7, p.67); Algorithm 3 is deterministic
--   - reading: T_arith ≤ Õ(mn² + n⁵⁶), Õ suppressing logarithmic factors in m, n → realOps ≤ C(mn² + n⁵⁶)(log(m + n + 2))^k with C, k ∈ ℕ fixed before the input; reason: the standard meaning of Õ with the stated logarithmic factors
--   - reading: rational inputs of every size → n ≥ 1 in part (b); reason: at n = 0 the printed bound is 0, while writing m output signs requires reading m with comparisons; the bound is meant for n ≥ 1 (part (a) keeps n = 0)
--   - generalization: a bound on arithmetic operations → also the total number of executed steps is ≤ C(m + n + 2)^k; reason: the title's polynomial running time; it implies the printed arithmetic bound unchanged
--   - encoding: rational inputs A_i; output signs σ → every entry has rational real and imaginary parts; input layout m n A; σ = the m output cells, each the real 1 or −1, on every tape ω; reason: the machine stores reals; an admissible program makes no random draws, so the tape is irrelevant
--   - reading: (c) the sign classes of σ (σ implicit) → for every σ ∈ {±1}^m satisfying (a)'s bound for A_i = a_ia_i*; reason: (c) uses the signs of (a)/(b) (proof p.71); with (a) this gives the partition, with (b) the arithmetic sentence
--   - encoding: ‖a_i‖² → ∑_j |a_ij|²; reason: same value
--   - encoding: operator norm ‖·‖ induced by the Euclidean norm; ‖X‖^{1/2} → AgnosticTNS.opNorm (sup of ‖Xv‖ over the Euclidean unit ball); Real.sqrt; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8, p.68 (PDF p.68); Theorem 1.1, p.3

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_IsRatC
import Definitions.Def_KSPolySign_layout
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Theorem 6.8 (Main result, formal version of Theorem 1.1).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8, p.68 (PDF p.68);
Theorem 1.1, p.3.

For Hermitian `A_1, …, A_m ∈ ℂ^{n×n}` of rank at most one:
(a) there are signs `σ ∈ {±1}^m` with `‖∑ σ_iA_i‖ ≤ 3.4814‖∑ A_i²‖^{1/2}`;
(b) for rational inputs, Algorithm 3 (deterministic) finds such signs in `Õ(mn² + n⁵⁶)` arithmetic
operations;
(c) if `A_i = a_ia_i*`, `∑ A_i = I` and `‖a_i‖² ≤ α`, the sign classes `I_1 = {σ_i = 1}`,
`I_2 = {σ_i = −1}` satisfy `‖∑_{i ∈ I_j} a_ia_i* − I/2‖ ≤ 1.7407√α`.

**Formalization Note** `‖·‖` is the Euclidean operator norm (`AgnosticTNS.opNorm`, published); `‖X‖^{1/2}` is `Real.sqrt`. (b): one `VecBalPoly.Admissible` program on the published real RAM
(rational literals, no square root, no random draws); arithmetic operations are `VecBalPoly.realOps`;
`Õ` suppresses logarithmic factors in `m, n`: `realOps ≤ C(mn² + n⁵⁶)(log(m + n + 2))^k` with `C, k`
fixed before the input; `n ≥ 1`. The run also halts within `C(m + n + 2)^k` steps in total (the
polynomial running time of the title). The input is `layout m n A` (real and imaginary parts of every
entry); a rational input has rational real and imaginary parts; the signs are the `m` output cells,
each the real `1` or `−1`. (c): stated for every signing `σ` meeting the bound of (a) for
`A_i = a_ia_i*`, which (a) and (b) produce; `‖a_i‖² = ∑_j |a_{ij}|²`. -/
theorem theorem_6_8 :
    (∀ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1) →
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • A i) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) ∧
    (∃ P : MatMulTimeLP.Program, VecBalPoly.Admissible P ∧ ∃ C k : ℕ,
      ∀ (m n : ℕ), 1 ≤ n → ∀ A : Fin m → Matrix (Fin n) (Fin n) ℂ,
        (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1 ∧ ∀ j l, IsRatC (A i j l)) →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout m n A) ω t ∧
          (VecBalPoly.realOps P (layout m n A) ω t : ℝ) ≤
            C * ((m : ℝ) * n ^ 2 + (n : ℝ) ^ 56) * Real.log (m + n + 2) ^ k ∧
          ((t + 1 : ℕ) : ℝ) ≤ C * ((m : ℝ) + n + 2) ^ k ∧
          (∀ i, MatMulTimeLP.outputAt P (layout m n A) ω t m i = 1 ∨ MatMulTimeLP.outputAt P (layout m n A) ω t m i = -1) ∧
          AgnosticTNS.opNorm (∑ i, ((MatMulTimeLP.outputAt P (layout m n A) ω t m i : ℝ) : ℂ) • A i) ≤
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) ∧
    ∀ (m n : ℕ) (a : Fin m → Fin n → ℂ) (α : ℝ),
      ∑ i, Matrix.vecMulVec (a i) (star (a i)) = 1 → (∀ i, ∑ j, ‖a i j‖ ^ 2 ≤ α) →
      ∀ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) →
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • Matrix.vecMulVec (a i) (star (a i))) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, Matrix.vecMulVec (a i) (star (a i)) * Matrix.vecMulVec (a i) (star (a i)))) →
        ∀ s : ℝ, (s = 1 ∨ s = -1) →
          AgnosticTNS.opNorm ((∑ i ∈ Finset.univ.filter (fun i => σ i = s), Matrix.vecMulVec (a i) (star (a i))) -
            (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 1.7407 * Real.sqrt α := by sorry

end KSPolySign
