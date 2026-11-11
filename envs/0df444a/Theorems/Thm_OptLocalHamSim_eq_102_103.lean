-- Prove2me | Theorems.Thm_OptLocalHamSim_eq_102_103
-- name    : OptLocalHamSim.eq_102_103
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:34:02.025064+00:00
-- url     : https://prove2.me/theorems/bbd21c65-7154-466c-8dda-db653da5d061
-- title:
--   Eqs. (102)–(103) — telescoping: $\|V_s\cdots V_1\iota_0-\iota_0U_s\cdots U_1\|\le\sum_j\|V_j\iota_0-\iota_0U_j\|\le\sum_j\eta_j$
-- statement:
--   For matrices $V_1,\dots,V_s$ on the full space, $U_1,\dots,U_s$ on the data, and the embedding $\iota_0$,
--
--   $$
--   V_s\cdots V_1\iota_0-\iota_0U_s\cdots U_1=\sum_{j=1}^sV_s\cdots V_{j+1}\bigl(V_j\iota_0-\iota_0U_j\bigr)U_{j-1}\cdots U_1 .
--   $$
--
--   If all $V_j$ and $U_j$ are unitary and $\|V_j\iota_0-\iota_0U_j\|\le\eta_j$, then
--
--   $$
--   \|V_s\cdots V_1\iota_0-\iota_0U_s\cdots U_1\|\le\sum_{j=1}^s\|V_j\iota_0-\iota_0U_j\|\le\sum_{j=1}^s\eta_j .
--   $$
--
--   The errors of the block calls add up over the whole circuit without any assumption on the intermediate ancilla states.
--
--   Differences from the source:
--   - generalization: the identity (102) for the block circuits, their ideal evolutions and the embedding ι₀ → the identity for arbitrary matrices V_j, U_j and any matrix ι; (103) for unitary V_j, U_j and any ι; reason: the identity is algebraic; the bound uses only unitarity
--   - encoding: V_s ⋯ V_{j+1}, U_{j−1} ⋯ U_1 → descProd of sequences indexed by ℕ (indices 1, …, s); reason: the same products
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), eqs. (102)–(103), p.36

import Mathlib
import Definitions.Def_OptLocalHamSim_descProd

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Eqs. (102)–(103)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.36: the telescoping identity
V_s⋯V_1ι₀ − ι₀U_s⋯U_1 = ∑_{j=1}^s V_s⋯V_{j+1}(V_jι₀ − ι₀U_j)U_{j−1}⋯U_1 (102), and, for unitary
V_j, U_j with ‖V_jι₀ − ι₀U_j‖ ≤ η_j,
‖V_s⋯V_1ι₀ − ι₀U_s⋯U_1‖ ≤ ∑_{j=1}^s ‖V_jι₀ − ι₀U_j‖ ≤ ∑_{j=1}^s η_j (103).

**Formalization Note** The sequences are indexed by `1, …, s` (`V U : ℕ → Matrix`); `descProd X a k`
is `X_{a+k} ⋯ X_{a+1}`. The identity (102) is stated for arbitrary matrices and any `ι` in place of
`ι₀`; (103) assumes `V_j`, `U_j` unitary for `1 ≤ j ≤ s`. -/
theorem eq_102_103 {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : ℕ → Matrix m m ℂ) (U : ℕ → Matrix n n ℂ) (ι : Matrix m n ℂ) (s : ℕ) :
    descProd V 0 s * ι - ι * descProd U 0 s =
        ∑ j ∈ Finset.Icc 1 s, descProd V j (s - j) * (V j * ι - ι * U j) * descProd U 0 (j - 1) ∧
      ((∀ j ∈ Finset.Icc 1 s, V j ∈ Matrix.unitaryGroup m ℂ ∧ U j ∈ Matrix.unitaryGroup n ℂ) →
        ∀ η : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 s, ‖V j * ι - ι * U j‖ ≤ η j) →
          ‖descProd V 0 s * ι - ι * descProd U 0 s‖ ≤
              ∑ j ∈ Finset.Icc 1 s, ‖V j * ι - ι * U j‖ ∧
            ∑ j ∈ Finset.Icc 1 s, ‖V j * ι - ι * U j‖ ≤ ∑ j ∈ Finset.Icc 1 s, η j) := by sorry

end OptLocalHamSim
