-- Prove2me | Theorems.Thm_GeoQAC_eq_1_phase_circuit
-- name    : GeoQAC.eq_1_phase_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:03.46145+00:00
-- url     : https://prove2.me/theorems/e68b627c-0855-4e20-b870-d33808081de2
-- title:
--   Display (1) — exact computation yields $|\chi_f\rangle$ at depth $2d$
-- statement:
--   Suppose a depth-$d$ $[w,h]$-2D-QAC circuit $C$ computes $f:\{0,1\}^n\to\{0,1\}$ exactly, and let $D=\mathrm{diag}(1,i)$ act on its output qubit. Since that qubit is in $|f(x)\rangle$, $C^\dagger DC|x,0^a\rangle=i^{f(x)}|x,0^a\rangle$, and therefore
--   $$
--   C^\dagger DC\big(|+\rangle^{\otimes n}|0^a\rangle\big)=|\chi_f\rangle|0^a\rangle. \tag{1}
--   $$
--   The resulting circuit has depth $2d$ on the same grid. Absorbing the preparation of $|+\rangle^{\otimes n}$ and of the ancillas into the first one-qubit layer, there is a depth-$2d$ $[w,h]$-2D-QAC circuit $C'$ with $C'|0\cdots0\rangle=|\chi_f\rangle\otimes|\text{ancillas}\rangle$.
--
--   Differences from the source:
--   - generalization: ancillas $|0^a\rangle$ → any product ancilla state $\bigotimes_v|a_v\rangle$ (output $|\chi_f\rangle\otimes\bigotimes_v|a_v\rangle$); reason: Theorem 3.14 applies (1) from product ancillas (p.26); $|a_v\rangle=|0\rangle$ gives the printed display.
--   - encoding: the circuit $C^\dagger DC$ applied to $|+\rangle^{\otimes n}|0^a\rangle$ → a circuit $C'$ started at $|0\cdots0\rangle$ whose first one-qubit layer prepares $|+\rangle^{\otimes n}$ and the ancillas; reason: p.26, "absorbing the product ancillary initialization into local gates"; the depth counts multi-qubit layers only.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), display (1), p.24; proof of Theorem 3.14, p.26

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_phaseState

namespace GeoQAC

open Matrix

/-- **Display (1)** (arXiv:2604.07178, version of 2026-11-03, p.24). Suppose a depth-`d` circuit `C`
computes `f` exactly, and let `D = diag(1, i)` act on its output qubit. Then
`C†DC(|+⟩^{⊗n}|0^a⟩) = |χ_f⟩|0^a⟩`, and the resulting circuit has depth `2d` on the same grid.

**Formalization Note.**
* Stated for a `[w, h]`-2D-QAC circuit computing `f` exactly from product ancillas `anc` (inputs at
  `inp`, output `out`), as Theorem 3.14 uses it; `|0^a⟩` is the special case `anc_v = |0⟩`.
* The `|+⟩^{⊗n}` and ancilla preparations are absorbed into the first one-qubit layer (p.26: "After
  absorbing the product ancillary initialization into local gates"), so the new circuit `C'` of depth
  `2d` on the same grid starts from `|0…0⟩` and outputs exactly `|χ_f⟩ ⊗ (⊗_{v ∉ inp} anc_v)`. -/
theorem eq_1_phase_circuit {w h d n : ℕ} (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
    (anc : Pos w h → Bool → ℂ) (out : Pos w h) (f : (Fin n → Bool) → Bool)
    (hC : C.Is2D) (hf : ComputesExactly C inp anc out f) :
    ∃ C' : QACCircuit (Pos w h) (2 * d), C'.Is2D ∧
      C'.matrix *ᵥ basisVec (fun _ => false) = embedInput inp anc (phaseState f) := by sorry

end GeoQAC
