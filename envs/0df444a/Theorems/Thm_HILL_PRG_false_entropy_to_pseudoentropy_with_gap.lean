-- Prove2me | Theorems.Thm_HILL_PRG_false_entropy_to_pseudoentropy_with_gap
-- name    : HILL.PRG.false_entropy_to_pseudoentropy_with_gap
-- status  : Open
-- author  : @Victorized
-- created : 2026-10-24T04:44:07.195323+00:00
-- url     : https://prove2.me/theorems/d8efa933-270e-4991-8fec-d6e8958fd1bc
-- title:
--   Lemma 4.16 — false entropy yields pseudoentropy
-- statement:
--   A mildly nonuniform false-entropy generator yields a mildly nonuniform pseudoentropy generator. In the formal model, both generators may have polynomial-time computable seed and output lengths, and their integer advice is polynomially bounded. The conclusion requires computational entropy exceeding the new seed length by a positive inverse-polynomial amount.
--
--   This theorem is an open dependency of the proposed proof of the mission main theorem, `HILL.PRG.theorem_6_3`; no proof is claimed here.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
--
--   The separate `PolyParam` condition explicitly requires a positive inverse-polynomial entropy gap. It is essential: the model predicates for pseudoentropy and false entropy do not impose it by themselves.
--
--   This corrects `HILL.PRG.false_entropy_to_pseudoentropy`, whose statement omitted the separate gap condition.
-- source:
--   Håstad, Impagliazzo, Levin, Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, p. 1381, Construction 4.15 and Lemma 4.16; https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf

import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- The existential consequence of Construction 4.15 and Lemma 4.16. -/
theorem false_entropy_to_pseudoentropy_with_gap :
    (∃ (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ), PolyParam s ∧ IsFalseEntropyGen F a s) →
      ∃ (G : FunEns) (b : ℕ → ℕ) (t : ℕ → ℝ), PolyParam t ∧ IsPseudoentropyGen G b t := by sorry

end HILL.PRG
