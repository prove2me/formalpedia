-- Prove2me | Theorems.Thm_HardyFiveAxioms_hermitian_mem_span_fiducialProjector
-- name    : HardyFiveAxioms.hermitian_mem_span_fiducialProjector
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T22:18:23.165318+00:00
-- url     : https://prove2.me/theorems/c50cd8c9-595b-4f5a-9123-34c562ba4f1e
-- title:
--   Every Hermitian operator is a real combination of the fiducial projectors
-- statement:
--   Every Hermitian $N\times N$ complex matrix $\hat A$ can be written as a real linear combination
--
--   $$\hat A=\sum_k a_k\hat P_k,\qquad a_k\in\mathbb R,$$
--
--   of Hardy's fiducial projectors $|n\rangle\langle n|$, $|mn\rangle_x\langle mn|$, $|mn\rangle_y\langle mn|$.
--
--   Section 5 uses this to represent states and measurements by real vectors: "Any Hermitean matrix can be written as a sum of these projection operators times real numbers, i.e. in the form $a\cdot\hat P$." Together with linear independence it shows that the $N^2$ projectors form a real basis of the Hermitian operators.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 6–8, Section 5 (paragraph before Eq. (11), text after Eq. (11), and Eqs. (26)–(27))

import Mathlib
import Definitions.Def_hardy2001_projectors

namespace HardyFiveAxioms

/-- Hardy 2001, Section 5: every Hermitian operator on `ℂᴺ` is a real linear combination of
the fiducial projectors `|n⟩⟨n|`, `|mn⟩ₓ⟨mn|`, `|mn⟩_y⟨mn|`. -/
theorem hermitian_mem_span_fiducialProjector (N : ℕ) (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.IsHermitian) :
    A ∈ Submodule.span ℝ (Set.range (fiducialProjector (N := N))) := by sorry

end HardyFiveAxioms
