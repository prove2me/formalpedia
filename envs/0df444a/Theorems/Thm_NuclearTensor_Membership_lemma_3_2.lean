-- Prove2me | Theorems.Thm_NuclearTensor_Membership_lemma_3_2
-- name    : NuclearTensor.Membership.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:17:56.700859+00:00
-- url     : https://prove2.me/theorems/8d3bb0e1-0379-4d88-9a10-46c785818450
-- title:
--   Lemma 3.2 — bipartite spectral compression
-- statement:
--   For finite-dimensional real Hilbert spaces $X,Y$, any tensor $S\in X\otimes Y$, and any $\eta>0$, a deterministic polynomial-time construction returns $V=\mathbb R^r$, an embedding $U:V\to X$, $\widetilde S=(U^\dagger\otimes I)S$, and $E=((I-UU^\dagger)\otimes I)S$ such that
--   $$S=(U\otimes I)\widetilde S+E,\quad r\le\eta^{-2}\|S\|_F^2,$$
--   $$|\langle E,x\otimes y\rangle|\le\eta\|x\|\|y\|\quad(x\in X,y\in Y),\qquad\|\widetilde S\|_F\le\|S\|_F,\quad U^\dagger U=I.$$
--   The selected directions have singular values strictly greater than the threshold. The target includes existence of an ordinary SVD service and finite execution of the array construction, uniformly in the threshold and input. It provides the one-cut interface used throughout the prefix construction.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.10, Lemma 3.2

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem lemma_3_2 : Nonempty Spectral ∧
    ∃ P : Program, ∀ (σ : Spectral) (A q : ℕ), 0 < A → 0 < q →
      ∃ B p : ℕ, 0 < B ∧ 0 < p ∧
      ∀ (a b : ℕ) (M : Mat a b) (η : ℝ), 0 < η →
        runsWithin σ none A q [] P [a, b] ([η] ++ encodeMat M)
          (B * (1 + a + b + a * b) ^ p)
          (fun s => ∃ (r : ℕ) (U : Mat a r),
            let D := σ a b M
            let T := contract U (flatten M)
            let E := flatten M - expand U T
            r = (kept D η).length ∧
            (∀ i t, U i t = selectedEntry D η i.val t.val) ∧
            outputIntegers s = [r] ∧
            outputReals s = encodeMat U ++ encodeVec T ++ encodeVec E ∧
            flatten M = expand U T + E ∧
            (r : ℝ) ≤ η ^ (-2 : ℤ) * frobenius M ^ 2 ∧
            (∀ (x : Vec a) (y : Vec b),
              |inner ℝ E (outer x y)| ≤ η * ‖x‖ * ‖y‖) ∧
            ‖T‖ ≤ frobenius M ∧ orthonormalColumns U) := by sorry

end NuclearTensor.Membership
