-- Prove2me | Theorems.Thm_GeoQAC_lemma_3_15
-- name    : GeoQAC.lemma_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:36.799312+00:00
-- url     : https://prove2.me/theorems/181032b0-9bd6-40bc-9e99-0fbbe9b8357f
-- title:
--   Lemma 3.15 — the sensitivity–variance identity and $\Gamma(\chi_f)\ge\mathrm{as}(f)^2/(nw)$
-- statement:
--   For every Boolean function $f:\{0,1\}^n\to\{0,1\}$, the phase state $|\chi_f\rangle$ satisfies
--   $$
--   \mathrm{Var}_{\chi_f}\Big(\sum_j X_j\Big)=2\cdot\mathbb E_x[s_f(x)^2]-\mathrm{as}(f)^2 ,
--   $$
--   where $X_j$ is the Pauli $X$ on qubit $j$. As a corollary, on a width-$w$ grid $[w]\times[h]$,
--   $$
--   \Gamma(\chi_f)\ge\frac{2\cdot\mathbb E_x[s_f(x)^2]-\mathrm{as}(f)^2}{nw}\ge\frac{\mathrm{as}(f)^2}{nw}.
--   $$
--
--   The identity turns a combinatorial quantity of $f$ into a variance of a circuit output, so that the bounds of Theorem 3.7 constrain $\mathrm{as}(f)$.
--
--   **Formalization Note** In the corollary the $n$ qubits of $|\chi_f\rangle$ sit at any injective placement in the grid and the remaining positions carry any product state; division is real division.
--
--   Differences from the source:
--   - generalization: $|\chi_f\rangle$ on a width-$w$ grid → $|\chi_f\rangle$ on any injective placement of its $n$ qubits, tensored with any product state on the other grid positions; reason: when the inputs fill the grid there are no other positions, which is the printed statement.
--   - encoding: the bounds $(\cdot)/(nw)$ → real division, so at $n=0$ both bounds read $0\le0$; reason: the source's expressions are undefined at $n=0$; no instance with $n\ge1$ changes.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Lemma 3.15, p.25

import Mathlib
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_GeoQAC_lmv
import Definitions.Def_GeoQAC_avgSens
import Definitions.Def_GeoQAC_phaseState
import Definitions.Def_GeoQAC_ComputesExactly

namespace GeoQAC

open DHRUniq (IsUnitVec)

open ObliviousRSP (pureState)

/-- **Lemma 3.15** (arXiv:2604.07178, version of 2026-11-03, p.25). For every Boolean function
`f : {0,1}^n → {0,1}`, the phase state `|χ_f⟩` satisfies
`Var_{χ_f}(∑_j X_j) = 2 · E_x[s_f(x)²] − as(f)²`. As a corollary, on a width-`w` grid,
`Γ(χ_f) ≥ (2 · E_x[s_f(x)²] − as(f)²)/(nw) ≥ as(f)²/(nw)`.

**Formalization Note.**
* The identity is on the `n` qubits `Fin n`; `X_j` is the Pauli `X` (`QAlgorithms.pauliX`) on qubit
  `j`.
* The corollary places `χ_f` on any injective placement `inp` of its `n` qubits in a `[w] × [h]` grid,
  tensored with any product state `⊗ anc_v` on the remaining positions (none when the inputs fill
  the grid, the paper's setting).
* Division is real division; at `n = 0` both bounds read `0 ≤ 0`. -/
theorem lemma_3_15 :
    (∀ (n : ℕ) (f : (Fin n → Bool) → Bool),
      var (pureState (phaseState f)) (∑ j, embed1 j QAlgorithms.pauliX) =
        2 * sensSqMean f - avgSens f ^ 2) ∧
    ∀ (n w h : ℕ) (f : (Fin n → Bool) → Bool) (inp : Fin n ↪ Pos w h)
      (anc : Pos w h → Bool → ℂ), (∀ v, (∀ i, inp i ≠ v) → IsUnitVec (anc v)) →
      (2 * sensSqMean f - avgSens f ^ 2) / ((n : ℝ) * w) ≤
          lmv (pureState (embedInput inp anc (phaseState f))) ∧
        avgSens f ^ 2 / ((n : ℝ) * w) ≤ (2 * sensSqMean f - avgSens f ^ 2) / ((n : ℝ) * w) := by sorry

end GeoQAC
