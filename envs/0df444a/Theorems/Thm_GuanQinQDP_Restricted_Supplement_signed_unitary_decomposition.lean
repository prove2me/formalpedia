-- Prove2me | Theorems.Thm_GuanQinQDP_Restricted_Supplement_signed_unitary_decomposition
-- name    : GuanQinQDP.Restricted.Supplement.signed_unitary_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:37:36.536568+00:00
-- url     : https://prove2.me/theorems/6635be94-fab9-4322-b66a-54281bab81dc
-- title:
--   Lemma 6.1 — signed unitary decomposition of a qubit channel on operators with $\operatorname{Tr}_1X=0$
-- statement:
--   Let $E$ be a qubit channel with Bloch matrix $\Theta$, and let $\|\Theta\|$ be its largest singular value.
--
--   1. If $\|\Theta\|>0$, there are probabilities $p_k$, signs $\epsilon_k\in\{\pm1\}$ and qubit unitaries $U_k$, at most eight of each, such that for every finite-dimensional system $R$ and every Hermitian $X$ on $\mathbb C^2\otimes R$ with $\operatorname{Tr}_1X=0$,
--   $$(E\otimes\mathrm{id}_R)(X)=\|\Theta\|\sum_kp_k\epsilon_k\,(U_k\otimes I)X(U_k\otimes I)^\dagger.$$
--   The $p_k,\epsilon_k,U_k$ depend only on $E$, not on $R$ or $X$.
--   2. If $\|\Theta\|=0$, then $(E\otimes\mathrm{id}_R)(X)=0$ for every such $R$ and $X$.
--
--   On differences of states with equal marginals on the complement, any qubit channel thus acts as $\|\Theta\|$ times a signed average of unitary conjugations. This is the key step of the exact contraction of the transport norms (Theorem 6.2).
--
--   Differences from the source:
--
--   - encoding: R a finite-dimensional Hilbert space, X on C² ⊗ R → R : Type with [Fintype R] [DecidableEq R], X : Matrix (Qubit × R) (Qubit × R) ℂ; reason: every finite-dimensional space is ℂ^R for a finite index type
--   - encoding: Bloch matrix Θ with E(σ_b) = ∑_a Θ_ab σ_a; ∥Θ∥ its largest singular value → blochMatrix E with entries ½ Re Tr[σ_a E(σ_b)]; specNorm = operator norm on Euclidean ℝ³; reason: E(σ_b) is Hermitian and traceless for a channel, so its Pauli coefficients are these; the Euclidean operator norm is the largest singular value
--   - encoding: probabilities p_k, signs ϵ_k ∈ {±1}, qubit unitaries U_k, at most eight of each → m ≤ 8 and p, ε : Fin m → ℝ, U : Fin m → unitaryGroup, p_k ≥ 0, ∑ p_k = 1, ε_k = 1 ∨ ε_k = −1, chosen before R and X; reason: the source fixes the decomposition for E, uniformly in R and X
--   - encoding: (E ⊗ id_R)(X), Tr_1 X → applyFirst E X, traceLeft X; reason: the base definitions of the tensor extension on the first factor and of the partial trace over it
-- source:
--   Ji Guan, Yecheng Qin, Parallel Composition of Quantum Differential Privacy: The Role of Measurement Restrictions, STOC 2027 submission #1640 (October 2026), source.pdf SHA-256 da23c8347251683a16df4c61de3fa1604211cdbf34d757a7a45feb0efd54c694, Lemma 6.1 (printed p. 32 / PDF p. 33), proof in §A.3 (printed p. 38 / PDF p. 39)

import Definitions.Def_GuanQinQDP_Restricted_Supplement_Model
open QAlgorithms GuanQinQDP.Restricted WildeQIT.EntBreaking
open scoped Matrix ComplexOrder

namespace GuanQinQDP.Restricted.Supplement

/-- Lemma 6.1 (Signed unitary decomposition), Guan–Qin, STOC 2027 submission #1640, printed
p. 32 / PDF p. 33 (proof in §A.3, printed p. 38 / PDF p. 39).

Let `E` be a qubit channel with Bloch matrix `Θ`.

1. If `∥Θ∥ > 0`, there are at most eight probabilities `p_k` (`p_k ≥ 0`, `∑ p_k = 1`), signs
   `ϵ_k ∈ {±1}` and qubit unitaries `U_k`, chosen once, such that for every finite system `R` and
   every Hermitian `X` on `ℂ² ⊗ R` with `Tr_1 X = 0`,
   `(E ⊗ id_R)(X) = ∥Θ∥ ∑_k p_k ϵ_k (U_k ⊗ I) X (U_k ⊗ I)†`.
2. If `∥Θ∥ = 0`, then `(E ⊗ id_R)(X) = 0` for every such `R` and `X`. -/
theorem signed_unitary_decomposition (E : Matrix Qubit Qubit ℂ →ₗ[ℂ] Matrix Qubit Qubit ℂ)
    (hE : IsQuantumChannel E) :
    (0 < specNorm (blochMatrix ⇑E) →
      ∃ m : ℕ, m ≤ 8 ∧ ∃ (p ε : Fin m → ℝ) (U : Fin m → Matrix Qubit Qubit ℂ),
        (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧ (∀ k, ε k = 1 ∨ ε k = -1) ∧
          (∀ k, U k ∈ Matrix.unitaryGroup Qubit ℂ) ∧
          ∀ (R : Type) [Fintype R] [DecidableEq R] (X : Matrix (Qubit × R) (Qubit × R) ℂ),
            X.IsHermitian → traceLeft X = 0 →
              applyFirst ⇑E X = ((specNorm (blochMatrix ⇑E) : ℝ) : ℂ) •
                ∑ k, ((p k * ε k : ℝ) : ℂ) •
                  (Matrix.kronecker (U k) (1 : Matrix R R ℂ) * X *
                    (Matrix.kronecker (U k) (1 : Matrix R R ℂ))ᴴ)) ∧
    (specNorm (blochMatrix ⇑E) = 0 →
      ∀ (R : Type) [Fintype R] [DecidableEq R] (X : Matrix (Qubit × R) (Qubit × R) ℂ),
        X.IsHermitian → traceLeft X = 0 → applyFirst ⇑E X = 0) := by sorry

end GuanQinQDP.Restricted.Supplement
