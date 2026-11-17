-- Prove2me | Theorems.Thm_OptLocalHamSim_Supplement_theorem_17
-- name    : OptLocalHamSim.Supplement.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:18:04.610433+00:00
-- url     : https://prove2.me/theorems/9ef4b488-659c-47c7-b350-04daa681cea3
-- title:
--   Theorem 17 — every nearest-neighbor circuit simulating uniform XXZ dynamics has depth $\ge c_{\mathrm{lb}}\min\{\ell_{\mathrm{sys}},\ \mathcal T+\log(n/\epsilon)/\log(e+\log(n/\epsilon)/\mathcal T)\}$
-- statement:
--   Fix a dimension $D\ge1$ and $\Delta_0\ge0$. Consider the cube $\Lambda=\{1,\dots,\ell_{\mathrm{sys}}\}^D$ with one qubit per site, so $n=\ell_{\mathrm{sys}}^D$, and the uniform XXZ Hamiltonian of Eq. (3)
--   $$
--   H_{\mathrm{XXZ}}=J_{\mathrm{hop}}\sum_{\langle x,y\rangle}\Big(\frac{X_xX_y+Y_xY_y}{2}+\Delta\,Z_xZ_y\Big),\qquad J_{\mathrm{hop}}=\frac{J}{2D(1+\Delta_0)},\quad |\Delta|\le\Delta_0 .
--   $$
--   Let $\mathcal T=\max\{1,\lceil J|T|\rceil\}$ be the time count of Eq. (5).
--
--   There are constants $c_{\mathrm{time}},c_{\mathrm{lb}},\epsilon_{\mathrm{lb}}>0$ and $\ell_0$, depending only on $D$ and $\Delta_0$, such that the following holds. Suppose
--   $$
--   \ell_{\mathrm{sys}}\ge\ell_0,\qquad 2D(1+\Delta_0)\le J|T|\le c_{\mathrm{time}}\,\ell_{\mathrm{sys}},\qquad 0<\epsilon\le\epsilon_{\mathrm{lb}} .
--   $$
--   Let $\mathcal U$ be any nearest-neighbour circuit (one-qubit gates and CNOTs between qubits at equal or adjacent sites), with any number $K$ of ancillary qubits at every site, such that
--   $$
--   \big\|\mathcal U\iota_0-\iota_0e^{-iH_{\mathrm{XXZ}}T}\big\|\le\epsilon ,
--   $$
--   where $\iota_0$ prepares all ancillas in $|0\rangle$ and $\|\cdot\|$ is the operator norm. Then the depth $d$ of $\mathcal U$ satisfies
--   $$
--   d\;\ge\;c_{\mathrm{lb}}\min\Big\{\ell_{\mathrm{sys}},\ \mathcal T+\frac{\log(n/\epsilon)}{\log\big(e+\log(n/\epsilon)/\mathcal T\big)}\Big\}.
--   $$
--
--   The bound holds for every $\Delta$ with $|\Delta|\le\Delta_0$, both signs of $T$ and of $\Delta$, and every ancilla budget. At fixed time and constant error it gives depth $\Omega(\log n/\log\log n)$, which matches the $O(\log n)$ depth of Theorem 16 up to a $\log\log n$ factor; it is an unconditional geometric obstruction for an explicit interacting model.
--
--   **Formalization Note** The cube is `Site (fun _ => ℓ)` (sites $0,\dots,\ell-1$ in each coordinate), $n$ is `numQubits _ 1` $=\ell^D$, $\mathcal T$ is the published `timeCount J T`, $\log$ is the natural logarithm and $e=\exp 1$. The circuit is a published `ConstDepthUnitary.Circuit` on the wires $(\Lambda\times\{0\})\sqcup(\Lambda\times\mathrm{Fin}\,K)$ satisfying the published `IsNN` (no fan-out), its depth is its number of layers, and the error is the operator norm of the full output, ancillas included. The constants are chosen before $\Delta$, $J$, $\ell_{\mathrm{sys}}$, $T$, $\epsilon$, $K$ and the circuit. $J>0$ is not a separate hypothesis: it follows from $J|T|\ge 2D(1+\Delta_0)>0$.
--
--   Differences from the source:
--   - encoding: $\Lambda=\{1,\dots,\ell_{\mathrm{sys}}\}^D$ → sites $\{0,\dots,\ell_{\mathrm{sys}}-1\}^D$ (`Site (fun _ => ℓ)`); reason: a translation, the lattice metric and every nearest-neighbour pair are unchanged.
--   - encoding: "every circuit satisfying Eq. (2)" → every `IsNN` circuit (one-qubit gates and CNOTs at ℓ¹ site distance ≤ 1, no fan-out) for every number $K$ of ancillas per site, as in the published goal; reason: this is the mission's reading of the nearest-neighbour circuit of Eq. (2); any fixed-range two-qubit gate is a bounded-depth block of such gates (with CNOT-SWAP chains), so the class changes depth only by a constant factor absorbed into $c_{\mathrm{lb}}$.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), Theorem 17, p.37 (PDF p.37), eqs. (104)–(105); Eq. (2), p.5; Eq. (3), p.6; Eq. (5), p.11

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_OptLocalHamSim_Site
import Definitions.Def_OptLocalHamSim_IsLocalHam
import Definitions.Def_OptLocalHamSim_IsNN
import Definitions.Def_OptLocalHamSim_Supplement_hXXZ

open scoped Matrix.Norms.L2Operator

namespace OptLocalHamSim.Supplement

open OptLocalHamSim

/-- **Theorem 17 (Worst-case geometric depth lower bound)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an
Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation*, STOC 2027 submission (held
version, sha256 44a9768a…), p.37 (PDF p.37). Fix `D ≥ 1` and `∆₀ ≥ 0`. There are constants
`c_time, c_lb, ϵ_lb > 0` and `ℓ₀`, depending only on these fixed choices, such that the following
holds. If `ℓ_sys ≥ ℓ₀`, `2D(1 + ∆₀) ≤ J|T| ≤ c_time ℓ_sys`, `0 < ϵ ≤ ϵ_lb` (104), then every circuit
satisfying Eq. (2) for `H = H_XXZ` has depth
`d ≥ c_lb min{ℓ_sys, 𝒯 + log(n/ϵ) / log(e + log(n/ϵ)/𝒯)}` (105).

**Formalization Note**
* Uniform form (p.37): `|∆| ≤ ∆₀` with `J_hop = J/[2D(1 + ∆₀)]` fixed; `∆₀ = |∆|` is the literal
  choice of Eq. (3). The constants are chosen before `∆`, `J`, `ℓ_sys`, `T`, `ϵ`, the number `K` of
  ancillas per site and the circuit.
* The lattice is the cube `Site (fun _ => ℓ_sys)` (0-based translate of `{1,…,ℓ_sys}^D`), one data
  qubit per site, `n = numQubits _ 1 = ℓ_sys^D`.
* "Every circuit satisfying Eq. (2)": every nearest-neighbor circuit (`IsNN`: one-qubit gates and
  CNOTs at ℓ¹ site distance ≤ 1, no fan-out) on the wires `(Λ × Fin 1) ⊕ (Λ × Fin K)`, for every `K`,
  with `‖𝒰ι₀ − ι₀e^{−iH_XXZ T}‖ ≤ ϵ` in operator norm on the full output (ancillas included).
* `𝒯 = timeCount J T = max{1, ⌈J|T|⌉}` (Eq. (5)); `log` is the natural logarithm and `e = exp 1`;
  depth is the number of layers. -/
theorem theorem_17 (D : ℕ) (hD : 1 ≤ D) (Δ₀ : ℝ) (hΔ₀ : 0 ≤ Δ₀) :
    ∃ c_time c_lb ε_lb : ℝ, 0 < c_time ∧ 0 < c_lb ∧ 0 < ε_lb ∧ ∃ ℓ₀ : ℕ,
      ∀ (Δ : ℝ), |Δ| ≤ Δ₀ → ∀ (J : ℝ) (ℓ : ℕ), ℓ₀ ≤ ℓ → ∀ T : ℝ,
        2 * (D : ℝ) * (1 + Δ₀) ≤ J * |T| → J * |T| ≤ c_time * (ℓ : ℝ) →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε_lb →
        ∀ (K : ℕ) (U : ConstDepthUnitary.Circuit (Wire (fun _ : Fin D => ℓ) 1 K)), IsNN U →
          ‖(U.matrix * iota0 (L := fun _ : Fin D => ℓ) (q := 1) (K := K) -
              iota0 (L := fun _ : Fin D => ℓ) (q := 1) (K := K) *
                evol (hXXZ (fun _ : Fin D => ℓ) (J / (2 * (D : ℝ) * (1 + Δ₀))) Δ) T :
              Matrix (Wire (fun _ : Fin D => ℓ) 1 K → Bool) (Dat (fun _ : Fin D => ℓ) 1 → Bool) ℂ)‖
            ≤ ε →
          c_lb * min (ℓ : ℝ)
              ((timeCount J T : ℝ) +
                Real.log ((numQubits (fun _ : Fin D => ℓ) 1 : ℝ) / ε) /
                  Real.log (Real.exp 1 +
                    Real.log ((numQubits (fun _ : Fin D => ℓ) 1 : ℝ) / ε) / (timeCount J T : ℝ)))
            ≤ (U.depth : ℝ) := by sorry

end OptLocalHamSim.Supplement
