-- Prove2me | Theorems.Thm_OptLocalHamSim_lemma_11
-- name    : OptLocalHamSim.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:09.247221+00:00
-- url     : https://prove2.me/theorems/1d206572-d585-4871-9224-4ad7e05d3da0
-- title:
--   Lemma 11 — a fixed permutation of $k$ qubits on a path in depth $O(k)$ with $O(k^2)$ adjacent SWAPs
-- statement:
--   There is a constant $C>0$ such that for every $k$ and every permutation $\sigma$ of $\{0,\dots,k-1\}$ there is a circuit on exactly $k$ qubits arranged on a path, all of whose gates are SWAP gates on adjacent qubits ($|i-j|=1$), with depth at most $Ck$ and at most $Ck^2$ gates, which implements the permutation exactly: the qubit at position $i$ is moved to position $\sigma(i)$.
--
--   Such fixed SWAP networks align registers in the nearest-neighbor implementation without consulting quantum data.
--
--   Differences from the source:
--   - encoding: a nearest-neighbor path of k qubits, no auxiliary qubits → the wires Fin k, adjacency |i − j| = 1, and no other wires; reason: the same path
--   - encoding: an exact implementation of a prescribed permutation → the circuit matrix equals the permutation matrix sending the basis state y to y ∘ σ⁻¹; reason: the qubit at position i moves to σ(i); as σ is arbitrary, the other convention is the case σ⁻¹
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Lemma 11, p.25

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_OptLocalHamSim_IsNN

namespace OptLocalHamSim

/-- **Lemma 11 (Fixed path permutations; [CSU19, Section 3.1])**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.25. A prescribed permutation
of k qubits on a nearest-neighbor path has an exact implementation of depth O(k) using O(k²) adjacent
SWAP gates and no auxiliary qubits.

**Formalization Note** The path is the wires `Fin k` (no other wires: no auxiliary qubits), adjacent
means indices differing by one, and every gate is a SWAP on an adjacent pair. The circuit's matrix is
the permutation of qubits by `σ`: the qubit at position `i` moves to position `σ i`, i.e. the basis
state `y` goes to `y ∘ σ⁻¹`. The constant `C` is uniform in `k` and `σ`. -/
theorem lemma_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (σ : Equiv.Perm (Fin k)),
      ∃ U : ConstDepthUnitary.Circuit (Fin k),
        (∀ l ∈ U, ∀ g ∈ l.gates, ∃ (i j : Fin k) (hij : i ≠ j),
          g = ConstDepthUnitary.Gate.two i j hij swap ∧ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)) ∧
        (U.depth : ℝ) ≤ C * k ∧ (U.size : ℝ) ≤ C * (k : ℝ) ^ 2 ∧
        ConstDepthUnitary.Circuit.matrix U = Matrix.of fun x y => if x = y ∘ σ.symm then 1 else 0 := by sorry

end OptLocalHamSim
