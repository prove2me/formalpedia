-- Prove2me | Theorems.Thm_GGHRSW_ColoredMatrix_bookend_identity
-- name    : GGHRSW.ColoredMatrix.bookend_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:08:07.608351+00:00
-- url     : https://prove2.me/theorems/d59fba6b-52e6-4b78-8717-c1e1947a5eab
-- title:
--   Proof of Theorem 6, §C.3.1, p. 41 — bookend products reduce to (∏α)·s*(∏A)t* and (∏α′)·⟨s*′,t*′⟩
-- statement:
--   Let $p$ be prime and $BP$ a length-$n$ branching program, and fix any sample of $\mathcal{RND}_p(BP)$. For every choice of bits $b_1,\dots,b_n$,
--   $$\tilde{\mathbf s}\Big(\prod_{i=1}^n \tilde D_{i,b_i}\Big)\tilde{\mathbf t} = \Big(\prod_{i\in[n]}\alpha_{i,b_i}\Big)\cdot \mathbf s^*\Big(\prod_{i\in[n]}A_{i,b_i}\Big)\mathbf t^*$$
--   and
--   $$\tilde{\mathbf s}'\Big(\prod_{i=1}^n \tilde D'_{i,b_i}\Big)\tilde{\mathbf t}' = \Big(\prod_{i\in[n]}\alpha'_{i,b_i}\Big)\cdot \langle \mathbf s^{*\prime},\mathbf t^{*\prime}\rangle .$$
--   Here the products of matrices are taken in step order and $A_{i,b}$ denotes the $5\times5$ permutation matrix.
--
--   The randomizing matrices $R_i$ cancel, and the zero patterns of $\mathbf s$ and $\mathbf t$ remove every random diagonal entry, so the value of a $1\times1$ "bookend" product depends only on the bundling scalars, the permutation matrices and the 5-vectors. This is the starting point of the analysis of mixed-input attacks in the proof of Theorem 6.
--
--   **Formalization Note.** Steps are 0-based in Lean; the identity is stated for every sample, as the page's "corresponds to" is a deterministic identity.
-- source:
--   Garg, Gentry, Halevi, Raykova, Sahai and Waters, Candidate Indistinguishability Obfuscation and Functional Encryption for All Circuits, SIAM J. Comput. 45(3), 2016 (authors' version of July 21, 2013), p. 41, proof of Theorem 6, §C.3.1, case LC = 0 and RC = n + 2, second paragraph

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

namespace GGHRSW.ColoredMatrix

open Matrix

theorem bookend_identity (p : ℕ) [Fact p.Prime] (bp : BP) (ω : Sample p bp)
    (b : Fin bp.n → Bool) :
    (sTil ω * (List.ofFn fun i => DTil ω i (b i)).prod * tTil ω) 0 0 =
        (∏ i, alpha bp ω.γ i (b i)) *
          (ω.sStar ⬝ᵥ
            ((List.ofFn fun i => (bp.A i (b i)).permMatrix (ZMod p)).prod *ᵥ ω.tStar)) ∧
      (s'Til ω * (List.ofFn fun i => D'Til ω i (b i)).prod * t'Til ω) 0 0 =
        (∏ i, alpha' bp ω.γ i (b i)) * (ω.s'Star ⬝ᵥ ω.t'Star) := by sorry

end GGHRSW.ColoredMatrix
