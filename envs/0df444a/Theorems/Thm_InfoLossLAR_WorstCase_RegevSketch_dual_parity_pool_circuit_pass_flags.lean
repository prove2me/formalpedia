-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_dual_parity_pool_circuit_pass_flags
-- name    : InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_circuit_pass_flags
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T06:13:05.354166+00:00
-- url     : https://prove2.me/theorems/3f101ace-8c0d-4ff6-954c-accbe6e5ff58
-- title:
--   Uniform circuit for index-two dual certificate flags
-- statement:
--   Let $G$ be a uniform quantum polynomial-time sampler with classical output strings. For a nonsingular integer matrix $B$ of positive dimension $n$ and a positive rational threshold $\delta$, let $H_i$ double column $i$ of $B$. Put $D_i=\operatorname{adj}(H_i)^\mathsf{T}$, $r_i=|\det H_i|/(100\delta)$, and $m=(n+1)^3$. Let $p_i$ be the probability that the output of $G$ on the request $(D_i,r_i,m,16(n+1))$ starts with a coefficient pool that passes both tests. The odd-coordinate count at $i$ is at least $m/4$. For a decoded pool $(u_j)_{j=1}^m$, the covariance test is
--   $$
--   64\delta^2\sum_{j=1}^m\langle x,D_iu_j\rangle^2
--   \leq m\det(H_i)^2\|x\|_2^2\qquad (x\in\mathbb Z^n).
--   $$
--
--   There is a uniform quantum polynomial-time decision family $A$ such that, on each valid encoded input $(B,\delta)$, there is a probability mass function $w$ on Boolean flag vectors of length $n$ satisfying
--   $$
--   \sum_{t:t_i=1}w(t)=p_i\quad (1\leq i\leq n),
--   \qquad
--   \Pr[A(B,\delta)=1]=\sum_{t:\exists i,\,t_i=0}w(t).
--   $$
--   This flag law connects the exact circuit semantics for arbitrary sampler outputs to the finite probability estimate for the decision procedure.
-- source:
--   Circuit-realization sublemma for Prove2Me theorem InfoLossLAR.WorstCase.RegevSketch.dual_parity_pool_circuit_union (UUID 4fa11364-4184-412e-83a8-fa8693ba4b3e). Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, May 2, 2009, p. 30, Lemma 3.20 (https://cims.nyu.edu/~regev/papers/qcrypto.pdf), for the sampler-and-verifier structure. The exact flag interface is specific to the index-two certificate. De Wolf, Quantum Computing: Lecture Notes, §2.1.2 (https://homepages.cwi.nl/~rdewolf/qcnotes.pdf), for reversible classical evaluation in the quantum circuit model.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

theorem dual_parity_pool_circuit_pass_flags :
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
    ∃ weights : (Fin n → Bool) → ℝ,
      (∀ flags, 0 ≤ weights flags) ∧
      (∑ flags, weights flags) = 1 ∧
      (∀ i : Fin n,
        (∑ flags, if flags i then weights flags else 0) =
          outputProb G (dgsInput (D i) (r i) m (16*(n+1))) (decodedPoolEvent (E i))) ∧
      acceptProb A (encGapInstance B δ) =
        ∑ flags, if ∃ i : Fin n, flags i = false then weights flags else 0 := by sorry

end InfoLossLAR.WorstCase.RegevSketch
