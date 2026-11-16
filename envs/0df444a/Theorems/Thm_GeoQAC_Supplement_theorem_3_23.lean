-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_23
-- name    : GeoQAC.Supplement.theorem_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:26:04.536444+00:00
-- url     : https://prove2.me/theorems/a40dd430-5f8c-4c70-8900-dfff6f18b63a
-- title:
--   Theorem 3.23 — 1D-QAC MAJORITY and MOD need depth $\Omega(n)$
-- statement:
--   In the setting of Theorem 3.22 (a 1D-QAC circuit, inputs at arbitrary positions, ancillas in an arbitrary input-independent density matrix, one measured output qubit):
--
--   1. There are $c>0$ and $N$ such that for every $n\ge N$, every 1D-QAC circuit computing $\mathrm{MAJ}_n$ with success probability at least $2/3$ on every input has depth $d\ge c\,n$.
--   2. For every fixed modulus $r\ge2$ there are $c_r>0$ and $N_r$ such that for every $n\ge N_r$, every 1D-QAC circuit computing $\mathrm{MOD}_{r,n}$ with success probability at least $2/3$ on every input has depth $d\ge c_r\,n$.
--
--   Differences from the source:
--   - encoding: depth Ω(n) → c > 0 and threshold N (absolute for MAJORITY, depending on the fixed modulus r for MOD) with d ≥ c·n for n ≥ N; reason: asymptotic notation, with dependence on the fixed parameter r allowed (§2.1)
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.23, p.29

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_Supplement_hammingWeight
import Definitions.Def_GeoQAC_Supplement_outProb

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.23** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.29). "In the same
setting, MAJORITY and fixed-modulus MOD require depth `Ω(n)` for approximate computation."

**Formalization Note.**
* The setting of §3.7 (p.28): a `[1, h]`-2D-QAC circuit, inputs at any injective placement, any
  ancilla density matrix `σ` (mixed or entangled) on the non-input qubits, one output qubit.
  Approximate computation: success probability at least `2/3` on every input (Definition 2.4).
* MAJORITY: absolute `c > 0` and threshold `N`. MOD: for every fixed modulus `r ≥ 2` (p.26), a
  constant `c_r > 0` and threshold `N_r` depending on `r` (§2.1: dependence on fixed parameters). -/
theorem theorem_3_23 :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (d h : ℕ) (C : QACCircuit (Pos 1 h) d) (inp : Fin n ↪ Pos 1 h) (out : Pos 1 h)
        (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ),
        C.Is2D → IsDensityMatrix σ →
        (∀ x : Fin n → Bool, 2 / 3 ≤ outProb C inp σ out x (majFn n x)) →
          c * n ≤ d) ∧
    (∀ r : ℕ, 2 ≤ r → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (d h : ℕ) (C : QACCircuit (Pos 1 h) d) (inp : Fin n ↪ Pos 1 h) (out : Pos 1 h)
        (σ : Matrix (AncQ inp → Bool) (AncQ inp → Bool) ℂ),
        C.Is2D → IsDensityMatrix σ →
        (∀ x : Fin n → Bool, 2 / 3 ≤ outProb C inp σ out x (modFn r n x)) →
          c * n ≤ d) := by sorry

end GeoQAC.Supplement
