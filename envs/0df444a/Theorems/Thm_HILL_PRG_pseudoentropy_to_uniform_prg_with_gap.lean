-- Prove2me | Theorems.Thm_HILL_PRG_pseudoentropy_to_uniform_prg_with_gap
-- name    : HILL.PRG.pseudoentropy_to_uniform_prg_with_gap
-- status  : Open
-- author  : @Victorized
-- created : 2026-10-24T04:44:12.40678+00:00
-- url     : https://prove2.me/theorems/785cc2e3-6ca3-440b-9084-bfb133284994
-- title:
--   Sections 4.6 and 4.8 — pseudoentropy yields a uniform PRG
-- statement:
--   A mildly nonuniform pseudoentropy generator yields a uniform pseudorandom generator. This combines entropy extraction with advice removal. The target generator evaluates with advice identically zero and satisfies strict stretching and computational indistinguishability in the shared model. Normalization of the seed parameter and polynomial-time implementation are part of the assertion.
--
--   This theorem is an open dependency of the proposed proof of the mission main theorem, `HILL.PRG.theorem_6_3`; no proof is claimed here.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
--
--   The separate `PolyParam` condition explicitly requires a positive inverse-polynomial entropy gap. It is essential: the model predicates for pseudoentropy and false entropy do not impose it by themselves.
--
--   This corrects `HILL.PRG.pseudoentropy_to_uniform_prg`, whose statement omitted the separate gap condition.
-- source:
--   Håstad, Impagliazzo, Levin, Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, pp. 1380–1382, Theorem 4.14, Proposition 4.17, and subsection 4.9; https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf

import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- The existential composition of Theorem 4.14 with Proposition 4.17. -/
theorem pseudoentropy_to_uniform_prg_with_gap :
    (∃ (F : FunEns) (a : ℕ → ℕ) (s : ℕ → ℝ), PolyParam s ∧ IsPseudoentropyGen F a s) →
      ∃ G : FunEns, IsPRG G (fun _ => 0) := by sorry

end HILL.PRG
