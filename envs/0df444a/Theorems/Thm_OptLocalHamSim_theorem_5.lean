-- Prove2me | Theorems.Thm_OptLocalHamSim_theorem_5
-- name    : OptLocalHamSim.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:35:07.161552+00:00
-- url     : https://prove2.me/theorems/749f85ff-2a37-4957-b78e-8ae8d07027a3
-- title:
--   Theorem 5 — short-time block simulation to error $e^{-M}$ in depth $O(M)$, $O(vM)$ gates and $O(v)$ ancillas
-- statement:
--   Fix $D\ge1$, the number $q\ge1$ of data qubits per site, the range $R$, and constants $0<c_-\le c_+$. There are constants $M_0$, $C>0$ and a number $K$ of ancillas per site such that the following holds. For every real $M\ge M_0$, every rectangular block $\Lambda_{\mathrm{blk}}$ whose side lengths lie in $[c_-M,c_+M]$ (with $v=|\Lambda_{\mathrm{blk}}|$ sites), every Hamiltonian $H_{\mathrm{blk}}$ satisfying Eq. (1) with $J\le1$, and every $0<\tau\le1$, there is a nearest-neighbor circuit $\mathcal U$ on the data qubits and $K$ ancillas per site with
--
--   $$
--   \bigl\|\mathcal U\iota_0-\iota_0e^{-iH_{\mathrm{blk}}\tau}\bigr\|\le e^{-M},
--   $$
--
--   depth at most $CM$, at most $CvM$ gates, and $Kv\le Cv$ ancillas.
--
--   This is the paper's local simulation result (the precise form of Theorem 1): exponential accuracy in depth proportional to the block diameter.
--
--   Differences from the source:
--   - reading: a nearest-neighbor circuit (never defined formally) → a circuit on the wires (Λ × Fin q) ⊕ (Λ × Fin K) whose gates are one-qubit unitaries or CNOTs between wires at sites of ℓ¹ distance ≤ 1, with K ancillas at every site; reason: the paper's coarse-site model: exact one-qubit gates and nearest-neighbor CNOTs (p.12), a fixed number of ancillas per original site (p.37), gates between equal or adjacent coarse sites (eq. (155)); the constant-factor enlargements of §4 and App. A fold back onto Λ with bounded multiplicity, which only changes K
--   - reading: a classically specified nearest-neighbor circuit → the existence of a circuit (an explicit gate list); reason: the gate angles are real numbers, for which Lean has no computability notion
--   - reading: constants M₀ depending only on the local model and c₋, c₊; resources O(M), O(vM), O(v) → M₀, C and K depend only on D, q, R, c₋, c₊ and are fixed before M, the block, H and τ; reason: the O-constants are those of the fixed local model
--   - encoding: H_blk satisfies Eq. (1) with J ≤ 1 → IsLocalHam R 1 h; reason: local strength at most some J ∈ (0, 1] is local strength at most 1
--   - encoding: H = Σ_{Z⊆Λ} h_Z, each term on a nonempty declared set Z → one matrix h Z for every finite set of sites, with h Z ≠ 0 only on nonempty Z (so h ∅ = 0); reason: several terms on one Z are their sum; no instance changes
--   - encoding: Λ ⊂ ℤ^D a finite rectangular lattice → the box {0,…,L₁−1} × ⋯ × {0,…,L_D−1}; reason: a translate of Λ; the lattice metric is translation invariant
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Theorem 5, eqs. (10)–(11), p.12

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_IsNN

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Theorem 5 (Short-time block simulation)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.12. Fix constants 0 < c₋ ≤ c₊. Suppose H_blk
satisfies Eq. (1) with J ≤ 1 on a rectangular D-dimensional block Λ_blk whose side lengths lie in
[c₋M, c₊M], with v := |Λ_blk| sites. There is a constant M₀, depending only on the local model and
c₋, c₊, such that, for M ≥ M₀ and 0 < τ ≤ 1, a classically specified nearest-neighbor circuit 𝒰
satisfies ‖𝒰ι₀ − ι₀e^{−iH_blk τ}‖ ≤ e^{−M} (10) with depth O(M), gate count O(vM) and O(v)
ancillary qubits (11).

**Formalization Note**
* `M₀`, `C` and the number `K` of ancillas per site depend only on `D`, `q`, `R`, `c₋`, `c₊`.
  `M` is a free real parameter.
* "J ≤ 1" (with J > 0) is `IsLocalHam R 1 h`: local strength at most one.
* The circuit model is the goal's (`IsNN` on `Wire L q K`). "Classically specified" is read as the
  existence of an explicit gate list (a `ConstDepthUnitary.Circuit`); the gate angles are real, for
  which Lean has no computability notion. -/
theorem theorem_5 (D q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (R cm cp : ℝ) (hcm : 0 < cm)
    (hcmp : cm ≤ cp) :
    ∃ M₀ C : ℝ, 0 < C ∧ ∃ K : ℕ,
      ∀ M : ℝ, M₀ ≤ M → ∀ (L : Fin D → ℕ), (∀ j, cm * M ≤ (L j : ℝ) ∧ (L j : ℝ) ≤ cp * M) →
        ∀ h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ, IsLocalHam R 1 h →
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
          ∃ U : ConstDepthUnitary.Circuit (Wire L q K), IsNN U ∧
            (U.depth : ℝ) ≤ C * M ∧
            (U.size : ℝ) ≤ C * ((∏ j, L j : ℕ) : ℝ) * M ∧
            ((K * ∏ j, L j : ℕ) : ℝ) ≤ C * ((∏ j, L j : ℕ) : ℝ) ∧
            ‖(U.matrix * iota0 (L := L) (q := q) (K := K) - iota0 (L := L) (q := q) (K := K) * evol (Ham h) τ :
              Matrix (Wire L q K → Bool) (Dat L q → Bool) ℂ)‖ ≤ Real.exp (-M) := by sorry

end OptLocalHamSim
