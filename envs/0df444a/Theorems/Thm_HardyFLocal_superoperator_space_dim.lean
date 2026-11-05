-- Prove2me | Theorems.Thm_HardyFLocal_superoperator_space_dim
-- name    : HardyFLocal.superoperator_space_dim
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:38:57.936085+00:00
-- url     : https://prove2.me/theorems/c13adb41-689b-4a61-94bd-5bef69e71501
-- title:
--   §5, p.13 — $|\Omega^N|=N^4$
-- statement:
--   For a Hilbert space of dimension $N\ge1$, the real span of the completely positive, trace non-increasing maps on the $N\times N$ complex matrices is the real space of Hermiticity-preserving maps, and
--   $$\dim_{\mathbb R}=N^4.$$
--   For a qubit this gives the sixteen superoperators of the fiducial set.
--
--   This count is what makes a fiducial family of sixteen maps possible.
--
--   Differences from the source:
--   - reading: superoperators are "trace non-increasing maps on density operators that take allowed states to allowed states" → completely positive (finite Kraus form) and trace non-increasing; reason: the standard meaning; positivity alone fails on entangled inputs, which this lattice produces
--   - encoding: |Ω|² = 2⁴ for a qubit → |Ω²|, with the superscript naming the Hilbert space dimension N, and the statement is the real dimension of the Hermiticity-preserving maps; reason: the page says "the number of linearly independent superoperators needed to span the space of superoperators"
--   - encoding: N is the dimension of the Hilbert space of a system → the hypothesis 1 ≤ N; reason: a Hilbert space dimension is at least 1; the statement also holds at N = 0, so the hypothesis excludes no instance of the source
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, p.13

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **`|Ω^N| = N⁴`**, Hardy, arXiv:0804.0054v1, §5, p.13 ("We have |Ω^N| = N⁴ so for a qubit we have
|Ω²| = 2⁴. This is the number of linearly independent superoperators needed to span the space of
superoperators for a qubit").

For a Hilbert space of dimension `N ≥ 1`, the real span of the completely positive, trace
non-increasing maps is exactly the space of Hermiticity-preserving maps, and that space has real
dimension `N⁴`.

**Formalization Note** The printed `|Ω|²` is read as `|Ω²|`: the superscript names the Hilbert space
dimension (p.12–13). -/
theorem superoperator_space_dim (N : ℕ) (hN : 1 ≤ N) :
    Submodule.span ℝ {Φ : Op (Fin N) | IsCP Φ ∧ IsTraceNonIncreasing Φ} = hpMaps (Fin N) ∧
    Module.finrank ℝ (hpMaps (Fin N)) = N ^ 4 := by sorry

end HardyFLocal
