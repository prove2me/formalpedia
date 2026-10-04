-- Prove2me | Theorems.Thm_HardyFiveAxioms_fiducialProjector_card_linearIndependent
-- name    : HardyFiveAxioms.fiducialProjector_card_linearIndependent
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T21:46:25.763982+00:00
-- url     : https://prove2.me/theorems/ea0608eb-7b71-492c-9915-4ab05e9f8aba
-- title:
--   Hardy's $N^2$ fiducial projectors are linearly independent
-- statement:
--   For every $N$, there are exactly $N^2$ fiducial projectors
--
--   $$|n\rangle\langle n|\ (1\le n\le N),\qquad |mn\rangle_x\langle mn|,\ |mn\rangle_y\langle mn|\ (1\le m<n\le N),$$
--
--   and they are linearly independent over $\mathbb R$ as elements of the space of complex $N\times N$ matrices.
--
--   This is the claim of Section 5 that "this makes a total of $N^2$ projectors. It is clear that these projectors are linearly independent."
--
--   **Formalization Note** Linear independence is over $\mathbb R$, the field relevant to real combinations $a\cdot\hat P$ of Hermitian operators. The count refers to the index type of the family in `hardy2001_projectors`.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, p. 8, Section 5, Eqs. (26)–(27) and the sentences following Eq. (27)

import Mathlib
import Definitions.Def_hardy2001_projectors

namespace HardyFiveAxioms

/-- Hardy 2001, Section 5 (Eqs. (26)–(27)): there are `N²` fiducial projectors
`|n⟩⟨n|`, `|mn⟩ₓ⟨mn|`, `|mn⟩_y⟨mn|`, and they are linearly independent over `ℝ`. -/
theorem fiducialProjector_card_linearIndependent (N : ℕ) :
    Fintype.card (FiducialIndex N) = N ^ 2 ∧
      LinearIndependent ℝ (fiducialProjector (N := N)) := by sorry

end HardyFiveAxioms
