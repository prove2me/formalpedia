-- Prove2me | Theorems.Thm_GaussOptCVQKD_property_i_continuity_energy_sublevel
-- name    : GaussOptCVQKD.property_i_continuity_energy_sublevel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:02:03.689318+00:00
-- url     : https://prove2.me/theorems/383ffd0a-6e2b-4710-afd6-ecc495acf666
-- title:
--   Property i) — continuity of $K_\beta$ in trace norm (corrected: continuity relative to each energy sublevel)
-- statement:
--   Fix $\beta\in[0,1]$, a reconciliation direction, the measurement choices of Alice and Bob, and an energy level $e\ge0$. Then:
--
--   1. $K_\beta$ is continuous in trace norm relative to the energy sublevel
--   $$
--   \mathcal S_e=\{\rho\ \text{density}:\ \langle \hat n\rangle_\rho\le e\cdot|I|\}
--   $$
--   (mean photon number at most $e$ per mode), for every finite mode set $I$ and owner map: for every $\rho\in\mathcal S_e$ and $\varepsilon>0$ there is $\delta>0$ such that every $\sigma\in\mathcal S_e$ with $\|\sigma-\rho\|_1<\delta$ has $|K_\beta(\sigma)-K_\beta(\rho)|<\varepsilon$;
--   2. on $\mathcal S_e$ the three pieces of $K_\beta$ (the outcome mutual information, $S(\rho)$ and the averaged conditional entropy of the key party's measurement) are finite.
--
--   Lower semicontinuity on each sublevel is what the extremality theorem (4) needs; every state with a covariance matrix lies in some sublevel.
--
--   **Formalization Note** Continuity is the $\varepsilon$–$\delta$ predicate `OscillatorTraceContinuous (some e)` of Support50.P14; clause 2 makes the real-valued $K$ the paper's $K$ on the sublevel.
--
--   Differences from the source:
--
--   - correction: i) Continuity: K is continuous in trace norm on all states ('the continuity of von Neumann entropies implies the continuity of K') → K_β is trace-norm continuous relative to each energy sublevel {mean photon number ≤ e·|I|}; reason: false as printed: Alice and Bob homodyne x, DR, β = 1, ρ = vacuum (K = 0), ρ_n = (1 − 1/n)ρ + (1/n)σ_n with σ_n the two-mode squeezed vacuum of squeezing r_n = n²; ‖ρ_n − ρ‖₁ ≤ 2/n → 0, every ρ_n has finite second moments, I(a:b) ≥ (1/n)log cosh(2n²) − log 2 and χ_aE ≤ S(ρ_n) ≤ log 2, so K(ρ_n) ≥ 2n − 3 log 2 → ∞; on a sublevel the squeezing of the admixture is capped and the construction fails (Winter-type energy-constrained continuity)
--   - generalization: one mode per party ((6)), or N modes per party ((7)) → every finite mode set I with every owner map I → {Alice, Bob}; reason: N = 1 or N modes on each side is the special case of an owner map with one or N modes per party
--   - generalization: direct reconciliation with perfect efficiency, K = S(a:b) − S(a:E) ((6)) → both directions (DR, and RR with a ↔ b, A ↔ B, p.3) and every reconciliation efficiency β ∈ [0, 1] (K = βS(a:b) − S(a:E), (11), p.4); reason: the paper extends its claim to RR (p.3) and to (11) (p.4) in prose; β = 1 with DR is (6)
--   - encoding: 'If ‖ρ^(n) − ρ‖₁ ≤ ε …' (sequential form) → ε–δ continuity relative to the sublevel, plus finiteness of the three pieces on it; reason: ε–δ and sequential continuity agree in the trace-norm metric; finiteness makes the real-valued K the paper's K
--   - encoding: entropies and mutual information as real numbers → in nats, valued in [0, ∞] (Mathlib klDiv, published extendedEntropyNats), converted to reals in K; reason: same values where finite; the statement concludes or assumes the finiteness it needs
--   - encoding: quadratures x, p and the heterodyne outcome α → x = (a + a†)/√2, vacuum covariance I (Support50.P14); heterodyne outcome recorded as √2(Re α, Im α); outcome laws and conditional states characterized by characteristic functions; reason: Lean convention; mutual information and Holevo quantities are invariant under an invertible linear relabelling of outcomes
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Optimality of Gaussian attacks', property i) Continuity, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_GaussOptCVQKD_MeasurementModel
import Definitions.Def_GaussOptCVQKD_KeyRate

open scoped ENNReal
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel InDomain OscillatorTraceContinuous)

namespace GaussOptCVQKD

/-- **Property i) Continuity, corrected to energy sublevels**, García-Patrón, Cerf,
arXiv:quant-ph/0608032v1, "Optimality of Gaussian attacks", p.3: "i) Continuity: If
‖ρ^(n)_ĀB̄ − ρ_ĀB̄‖₁ ≤ ε, using Ulhmann's theorem … Finally, the continuity of von Neumann entropies
implies the continuity of K."

For every `β ∈ [0, 1]`, direction `r`, measurement choices `mA`, `mB` and energy level `e ≥ 0`:
1. `K_β` is trace-norm continuous relative to the energy sublevel
   `{ρ density : mean photon number ≤ e · |I|}`, on every finite mode set `I` with every owner
   map (the ε–δ form `OscillatorTraceContinuous (some e)` of Support50.P14);
2. on that sublevel the three pieces of `K_β` (outcome mutual information, `S(ρ)`, and the
   averaged conditional entropy of the key party's measurement) are finite.

**Formalization Note** As printed (continuity on all states) the property is false; see the
Differences list. Clause 2 makes the real-valued `K` the paper's `K` on the sublevel. -/
theorem property_i_continuity_energy_sublevel (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (r : Reconciliation) (mA mB : Measurement) (e : ℝ) (he : 0 ≤ e) :
    OscillatorTraceContinuous (some e) (keyRate β r mA mB) ∧
    ∀ (I : Type) [Fintype I] (owner : I → Fin 2) (ρ : OscillatorKernel I),
      InDomain (some e) ρ →
      mutualInfo owner ![mA, mB] ρ < ⊤ ∧ extendedEntropyNats ρ < ⊤ ∧
        holevoIntegral owner ![mA, mB] ρ r.keyParty r.otherParty < ⊤ := by sorry

end GaussOptCVQKD
