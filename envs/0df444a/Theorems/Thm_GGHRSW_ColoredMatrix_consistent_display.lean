-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_consistent_display
-- name    : GGHRSW.ColoredMatrix.consistent_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:02.746184+00:00
-- url     : https://prove2.me/theorems/d2873237-1c63-459b-9421-adddc30d6cef
-- title:
--   Proof of Theorem 6, §C.3.1, p. 43 — for Π ≠ I and (c, c′) ≠ 0, 1/p < Pr[c′⟨s*′,t*′⟩ + c·s*Πt* = 0] < 2/p
-- statement:
--   Let $p$ be prime, $\Pi$ a $5\times5$ permutation matrix with $\Pi\neq I$, and $c,c'\in\mathbb Z_p$ not both zero. Draw $(\mathbf s^*,\mathbf t^*,\mathbf s^{*\prime},\mathbf t^{*\prime})\in(\mathbb Z_p^5)^4$ uniformly among the quadruples with $\langle\mathbf s^*,\mathbf t^*\rangle = \langle\mathbf s^{*\prime},\mathbf t^{*\prime}\rangle$. Then
--   $$\frac1p < \Pr\big[c'\cdot\langle \mathbf s^{*\prime},\mathbf t^{*\prime}\rangle + c\cdot \mathbf s^*\,\Pi\,\mathbf t^* = 0\big] < \frac2p .$$
--
--   In the proof of Theorem 6 this controls the only cancellation that a primal and a dummy evaluation on the same rejected input could produce: whenever the program's product is a non-identity permutation, the corresponding scalar vanishes only with probability $O(1/p)$.
--
--   **Formalization Note.** The probability is the ratio of counts over the finite constraint set. Both inequalities are strict, as printed. The permutation matrix of $P\in S_5$ is Mathlib's `Equiv.Perm.permMatrix`; since $P$ ranges over all non-identity permutations, the choice between $P$ and $P^{-1}$ is immaterial.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 43, proof of Theorem 6, §C.3.1, Consistent Monomials, displayed inequality

import Mathlib

open Classical

namespace GGHRSW.ColoredMatrix

open Matrix

theorem consistent_display (p : ℕ) [Fact p.Prime] (P : Equiv.Perm (Fin 5)) (hP : P ≠ 1)
    (c c' : ZMod p) (hc : ¬(c = 0 ∧ c' = 0)) :
    let S := Finset.univ.filter fun x :
        (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) × (Fin 5 → ZMod p) =>
      x.1 ⬝ᵥ x.2.1 = x.2.2.1 ⬝ᵥ x.2.2.2
    let E := S.filter fun x =>
      c' * (x.2.2.1 ⬝ᵥ x.2.2.2) + c * (x.1 ⬝ᵥ (P.permMatrix (ZMod p) *ᵥ x.2.1)) = 0
    1 / (p : ℝ) < (E.card : ℝ) / S.card ∧ (E.card : ℝ) / S.card < 2 / (p : ℝ) := by sorry

end GGHRSW.ColoredMatrix
