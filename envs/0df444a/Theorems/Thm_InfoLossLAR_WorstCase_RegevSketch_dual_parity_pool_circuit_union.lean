-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_circuit_union
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_circuit_union
-- status  : Open
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-18T23:48:49.82857+00:00
-- url     : https://prove2.me/theorems/4fa11364-4184-412e-83a8-fa8693ba4b3e
-- title:
--   Uniform index-two dual certificate circuit with one-sided soundness
-- statement:
--   Construct a uniform decision circuit making one sampler call for each doubled-column basis. Verify prefix decoding, an odd-coordinate count, and a rational positive-semidefinite covariance bound using exact polynomial-time arithmetic. Reject only when every certificate passes; the probability of acceptance is bounded by the sum of single-call failure probabilities without independence assumptions. In a YES instance take a primitive coefficient vector of a shortest vector x and choose an odd coefficient i. Every passing odd sample for this branch has pairing with x in a half-integer coset after dividing by det H, hence squared pairing at least 1/4. At least one quarter odd forces mean square ≥1/16, whereas the covariance test forces it ≤1/64 since ‖x‖≤δ. Thus the circuit accepts every YES input even on malformed or adversarial sampler outputs. Uniformly build sampler circuits for all possible polynomially bounded computed input lengths, routing registers and selecting the relevant output. There is no Gaussian-correctness assumption and no approximation factor in this circuit statement.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, full version dated May 2, 2009, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. Lemma 3.20 and its preceding reduction from GapSVP to the promise GapCVP variant, full-version PDF p. 30; fixed-family substitution and explicit uniform decision algorithm. Alternative index-two parity and rational covariance specialization of the dual certificate.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_pool_circuit_union :
    ∀ G : MFamily, IsMQPT G → ∃ A : Family, IsQPT A ∧
    ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 → ∀ δ : ℚ, 0 < δ →
    let m := (n+1)^3
    let H (i : Fin n) : Matrix (Fin n) (Fin n) ℤ := fun a b => B a b * (if b = i then 2 else 1)
    let D (i : Fin n) := (H i).adjugate.transpose
    let r (i : Fin n) : ℚ := (Int.natAbs (H i).det : ℚ) / (100*δ)
    let E (i : Fin n) (p : Fin m → Fin n → ℤ) : Prop :=
      m ≤ 4 * (Finset.univ.filter (fun j => Odd (p j i))).card ∧
      ∀ x : Fin n → ℤ,
        64 * δ^2 * (∑ j, ((∑ a, x a * ((D i).mulVec (p j)) a : ℤ) : ℚ)^2) ≤
          (m : ℚ) * ((H i).det : ℚ)^2 * (∑ a, (x a : ℚ)^2)
    (lam1 B ≤ δ → acceptProb A (encGapInstance B δ) = 1) ∧
    acceptProb A (encGapInstance B δ) ≤ ∑ i : Fin n,
      (1-outputProb G (dgsInput (D i) (r i) m (16*(n+1))) (decodedPoolEvent (E i))) := by sorry

end InfoLossLAR.WorstCase.RegevSketch
