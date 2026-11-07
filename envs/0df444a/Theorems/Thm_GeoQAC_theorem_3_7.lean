-- Prove2me | Theorems.Thm_GeoQAC_theorem_3_7
-- name    : GeoQAC.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:48.389904+00:00
-- url     : https://prove2.me/theorems/e2e0e7ad-0d6b-4511-8eab-553d4e75cc13
-- title:
--   Theorem 3.7 — 2D-QAC outputs have $\Gamma\le(Kw^3)^d$
-- statement:
--   There is an absolute constant $K\ge2$ such that every state $|\psi\rangle=C|0^n\rangle$ synthesized by a depth-$d$, width-$w$ 2D-QAC circuit on $n$ qubits satisfies
--   $$
--   \Gamma(\psi)\le (Kw^3)^d .
--   $$
--   Here the circuit's $n=wh$ qubits fill the grid $[w]\times[h]$ and all start in $|0\rangle$, and the depth counts the multi-qubit layers.
--
--   The bound shows that narrow shallow 2D-QAC circuits cannot create states with large column-separated correlations.
--
--   Differences from the source: none.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.7, p.16

import Mathlib
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_lmv

namespace GeoQAC

open ObliviousRSP (pureState)

open Matrix

/-- **Theorem 3.7** (arXiv:2604.07178, version of 2026-11-03, p.16). There is an absolute constant
`K ≥ 2` such that every state `|ψ⟩ = C|0^n⟩` synthesized by a depth-`d`, width-`w` 2D-QAC circuit on
`n` qubits satisfies `Γ(ψ) ≤ (K w³)^d`.

**Formalization Note.** The circuit's qubits fill the grid `[w] × [h]` and all start in `|0⟩`
(`n = wh`). The depth `d` counts multi-qubit layers only. `K` is chosen before `w`, `h`, `d`
and `C`. -/
theorem theorem_3_7 : ∃ K : ℝ, 2 ≤ K ∧ ∀ (w h d : ℕ) (C : QACCircuit (Pos w h) d), C.Is2D →
    lmv (pureState (C.matrix *ᵥ basisVec (fun _ => false))) ≤ (K * (w : ℝ) ^ 3) ^ d := by sorry

end GeoQAC
