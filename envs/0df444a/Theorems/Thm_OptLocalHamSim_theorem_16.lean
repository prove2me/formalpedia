-- Prove2me | Theorems.Thm_OptLocalHamSim_theorem_16
-- name    : OptLocalHamSim.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:15.761197+00:00
-- url     : https://prove2.me/theorems/69b72c3a-ba8d-454b-bc5b-46a21397cac3
-- title:
--   Theorem 16 — nearest-neighbor simulation of $e^{-iHT}$ in depth $O(\mathcal TM)$ with $O(n\mathcal TM)$ gates and $O(n)$ ancillas, $M=\log(2+n\mathcal T/\epsilon)$
-- statement:
--   Fix the dimension $D\ge1$, the number $q\ge1$ of data qubits per site and the range $R$. There are constants $c_1>0$, $C>0$ and a number $K$ of ancillas per site such that the following holds. Let $\Lambda$ be a rectangular lattice with $n=q|\Lambda|$ qubits, $J>0$, $H=\sum_Zh_Z$ a Hamiltonian satisfying Eq. (1), $T\in\mathbb R$ and $\epsilon\in(0,1)$, and put
--
--   $$
--   \mathcal T:=\max\{1,\lceil J|T|\rceil\},\qquad M:=\log\bigl(2+n\mathcal T/\epsilon\bigr).
--   $$
--
--   If every side of $\Lambda$ is at least $c_1M$, there is a nearest-neighbor circuit $\mathcal U$ on the data qubits and $K$ ancillas per site (one-qubit gates and CNOTs between equal or adjacent sites) with
--
--   $$
--   \bigl\|\mathcal U\iota_0-\iota_0e^{-iHT}\bigr\|\le\epsilon,
--   $$
--
--   depth at most $C\mathcal TM$, at most $Cn\mathcal TM$ gates, and $K|\Lambda|\le Cn$ ancillary qubits.
--
--   This is the paper's global simulation bound (the precise form of Theorem 2): it reduces the $\log^D$ overhead of Haah–Hastings–Kothari–Low to a single logarithm, with bounded ancilla density and an error bound on the entire output, ancillas included.
--
--   Differences from the source:
--   - encoding: M := c₀ log(2 + n𝒯/ϵ) with a sufficiently large model-dependent c₀ → M = log(2 + n𝒯/ϵ), with c₀ absorbed into c₁ and C; reason: for fixed c₀ the bounds c₁c₀M′ and C c₀M′ have the same form; every constant stays uniform
--   - reading: O(·) bounds and a sufficiently large constant c₁ → c₁, C and K depend only on D, q, R and are fixed before Λ, J, H, T and ϵ; reason: the O-constants of a fixed local model; J enters only through 𝒯
--   - reading: a nearest-neighbor circuit (never defined formally) → a circuit on the wires (Λ × Fin q) ⊕ (Λ × Fin K) whose gates are one-qubit unitaries or CNOTs between wires at sites of ℓ¹ distance ≤ 1, with K ancillas at every site; reason: the paper's coarse-site model: exact one-qubit gates and nearest-neighbor CNOTs (p.12), a fixed number of ancillas per original site (p.37), gates between equal or adjacent coarse sites (eq. (155)); the constant-factor enlargements of §4 and App. A fold back onto Λ with bounded multiplicity, which only changes K
--   - reading: The ancillary qubits have bounded spatial density and are reused throughout the circuit → K ancillas at every site, a wire set fixed for the whole circuit, and the clause K·|Λ| ≤ C·n; reason: bounded density is a constant number per site (p.37); reuse is the fixed ancilla register of the whole circuit
--   - encoding: an n-qubit lattice Hamiltonian with a fixed number of data qubits at each site → q ≥ 1 data qubits per site, n = q·|Λ|; reason: the same count
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
--   - encoding: Λ ⊂ ℤ^D a finite rectangular lattice → the box {0,…,L₁−1} × ⋯ × {0,…,L_D−1}; reason: a translate of Λ; the lattice metric is translation invariant
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Theorem 16, eq. (100), p.36

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_IsNN

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Theorem 16 (Simulation on a large lattice)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.36 (PDF p.36). Let H satisfy Eq. (1), with
𝒯, M as in Eq. (5). If every side of the lattice rectangle has length at least c₁M for a sufficiently
large constant c₁, then the simulation problem in Eq. (2) has a nearest-neighbor solution with circuit
depth d = O(𝒯M), gate count g = O(n𝒯M), ancillary qubits a = O(n).

**Formalization Note**
* Constants: `c₁`, `C` and the number `K` of ancillas per site are chosen before the lattice, the
  Hamiltonian, `J`, `T` and `ϵ`, and depend only on `D`, `q` and `R`. The scale is
  `M = log(2 + n𝒯/ϵ)` with the model constant `c₀` of (5) absorbed into `c₁` and `C`.
* `𝒯 = timeCount J T = max{1, ⌈J|T|⌉}` (a natural number); `n = q·∏ L_j` counts data qubits.
* The circuit acts on the wires `(Λ × Fin q) ⊕ (Λ × Fin K)` (data first), is nearest-neighbor
  (`IsNN`: one-qubit gates and CNOTs at ℓ¹ site distance ≤ 1, no fan-out), and its error is the
  operator norm of `𝒰ι₀ − ι₀e^{−iHT}` on the full output, ancillas included. "Bounded spatial
  density" is the fixed number `K` of ancillas per site; the ancilla count `K·|Λ|` is fixed for
  the whole circuit ("reused throughout").
* The Hamiltonian is one term `h Z` per set of sites `Z`, `h ∅ = 0` (`IsLocalHam`). -/
theorem theorem_16 (D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (R : ℝ) :
    ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∃ K : ℕ,
      ∀ (L : Fin D → ℕ) (J : ℝ)
        (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ),
        0 < J → IsLocalHam R J h →
        ∀ T ε : ℝ, 0 < ε → ε < 1 →
          (∀ j, c₁ * logScale (numQubits L q) (timeCount J T) ε ≤ (L j : ℝ)) →
          ∃ U : ConstDepthUnitary.Circuit (Wire L q K), IsNN U ∧
            (U.depth : ℝ) ≤
              C * (timeCount J T : ℝ) * logScale (numQubits L q) (timeCount J T) ε ∧
            (U.size : ℝ) ≤ C * (numQubits L q : ℝ) * (timeCount J T : ℝ) *
              logScale (numQubits L q) (timeCount J T) ε ∧
            ((K * ∏ j, L j : ℕ) : ℝ) ≤ C * (numQubits L q : ℝ) ∧
            ‖(U.matrix * iota0 (L := L) (q := q) (K := K) - iota0 (L := L) (q := q) (K := K) * evol (Ham h) T :
              Matrix (Wire L q K → Bool) (Dat L q → Bool) ℂ)‖ ≤ ε := by sorry

end OptLocalHamSim
