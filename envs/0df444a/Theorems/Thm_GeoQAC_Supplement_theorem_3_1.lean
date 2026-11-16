-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_1
-- name    : GeoQAC.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:21:50.668885+00:00
-- url     : https://prove2.me/theorems/b7a08d49-0368-4ebf-916c-e555754d5db4
-- title:
--   Theorem 3.1 — exact 2D simulation of QAC circuits; $\text{2D-QAC}^0=\mathrm{QAC}^0$
-- statement:
--   Let $U$ be the unitary of a depth-$d$ QAC circuit $C$ on $n$ qubits, with arbitrary (not geometrically local) gate supports. Then there are a $[n+1,n]$-2D-QAC circuit $V$ of depth $7d$ and a placement of $n$ data qubits on the $(n+1)\times n$ grid such that, for every vector $|\phi\rangle$ on $n$ qubits,
--   $$
--   V\big(|\phi\rangle\otimes|1^{n^2}\rangle\big)=\big(U|\phi\rangle\big)\otimes|1^{n^2}\rangle ,
--   $$
--   the $n^2$ workspace qubits starting and ending in $|1\rangle$. Consequently, for every family $L$ of Boolean functions, $L\in\text{2D-QAC}^0$ if and only if $L\in\mathrm{QAC}^0$.
--
--   Two-dimensional geometric locality therefore costs only a constant factor in depth and a polynomial number of qubits, which is why the paper studies the width of the grid.
--
--   Differences from the source:
--   - encoding: a depth-7d circuit → a circuit with exactly 7d multi-qubit layers, some possibly empty; reason: empty layers are allowed, so depth at most 7d and exactly 7d coincide
--   - reading: |ϕ⟩ ⊗ |1^{n²}⟩ without a stated placement → the data qubits sit at an injective placement chosen together with V; reason: the theorem leaves the placement to the construction (the proof uses row 0)
--   - encoding: QAC⁰ and 2D-QAC⁰ (Definitions 2.2, 2.3) → families of Boolean functions with ∃ d k ∀ n a depth-d circuit on ≤ k(n+1)^k qubits computing L_n with probability ≥ 2/3 on every input from |0⟩ ancillas, lengths n ≥ 0; reason: a depth-d circuit on q qubits has at most (2d+1)q gates, so polynomially many qubits is polynomial size; every length-0 function lies in both classes
--   - encoding: for every n-qubit input state |ϕ⟩ → for every vector ϕ on Fin n → Bool (not only unit vectors); reason: both sides are linear in ϕ, so the identity for unit vectors and for all vectors are equivalent
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.1, p.13

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_withOnes
import Definitions.Def_GeoQAC_Supplement_InQAC0

namespace GeoQAC.Supplement

open GeoQAC Matrix

/-- **Theorem 3.1** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.13). "Let `U` be a
unitary implemented by a depth-`d` QAC circuit on `n` qubits. There is a depth-`7d`
`[n + 1, n]`-2D-QAC circuit `V` that exactly simulates `U`: for every `n`-qubit input state `|ϕ⟩`,
`V(|ϕ⟩ ⊗ |1^{n²}⟩) = (U|ϕ⟩) ⊗ |1^{n²}⟩`. Consequently, `2D-QAC⁰ = QAC⁰`."

**Formalization Note.**
* `U` is `C.matrix` for a depth-`d` QAC circuit `C` on the qubits `Fin n` (all-to-all geometry).
* `V` is a circuit of depth exactly `7d` (layers may be empty) on the grid `Pos (n+1) n`
  (`n + 1` rows, `n` columns), with every multi-qubit support an interval. The `n` data qubits sit at
  an injective placement `data` chosen with `V`; every other qubit is workspace in `|1⟩`
  (`withOnes`). The identity is exact (no global phase) and holds for every vector `ϕ`.
* The class equality is `In2DQAC0 L ↔ InQAC0 L` for every family of Boolean functions `L`
  (Definitions 2.2, 2.3: constant depth, polynomially many qubits, success probability `≥ 2/3` on
  every input, `|0⟩` ancillas). Depth counts multi-qubit layers only. -/
theorem theorem_3_1 :
    (∀ (n d : ℕ) (C : QACCircuit (Fin n) d),
      ∃ (V : QACCircuit (Pos (n + 1) n) (7 * d)) (data : Fin n ↪ Pos (n + 1) n),
        V.Is2D ∧ ∀ ϕ : (Fin n → Bool) → ℂ,
          V.matrix *ᵥ withOnes data ϕ = withOnes data (C.matrix *ᵥ ϕ)) ∧
    (∀ L : (n : ℕ) → (Fin n → Bool) → Bool, In2DQAC0 L ↔ InQAC0 L) := by sorry

end GeoQAC.Supplement
