-- Prove2me | Theorems.Thm_GapAgnosticGS_eq_5
-- name    : GapAgnosticGS.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:30:59.717045+00:00
-- url     : https://prove2.me/theorems/47fb20e0-cb7e-494e-af3f-0aa375686aff
-- title:
--   Eq. (5) — hybrid bound for the first lower-bound family of Theorem 3.15
-- statement:
--   Let $\alpha>0$, $0<\Delta\le2\alpha$, $S\subseteq\{0,\dots,n-1\}$, $\tau=\pi/(4\alpha)$, and for $x\in S$ let
--
--   $$H^{(1)}_x=-\alpha|x\rangle\langle x|+(-\alpha+\Delta)\sum_{j\in S\setminus\{x\}}|j\rangle\langle j|+\alpha\sum_{j\notin S}|j\rangle\langle j|,\qquad H^{(1)}_{\rm ref}=(-\alpha+\Delta)\sum_{j\in S}|j\rangle\langle j|+\alpha\sum_{j\notin S}|j\rangle\langle j| .$$
--
--   Take any $T$-query algorithm, purified as an oracle circuit $|\Psi_{t+1}\rangle=V_tO|\Psi_t\rangle$ with oracle-independent unitaries $V_t$ and controlled phase-oracle queries $O$, started from one unit state. Let $|\Psi^x_T\rangle$ and $|\Psi^{\rm ref}_T\rangle$ be its final states with the oracles $e^{i\tau H^{(1)}_x}$ and $e^{i\tau H^{(1)}_{\rm ref}}$. Then
--
--   $$\Big(\sum_{x\in S}\big\||\Psi^x_T\rangle-|\Psi^{\rm ref}_T\rangle\big\|^2\Big)^{1/2}\le\frac{\pi\Delta}{4\alpha}\,T .\qquad(5)$$
--
--   Combined with the success requirement this gives $T=\Omega(\alpha\sqrt k/\Delta)$ for $|S|=k$, the first half of the lower bound of Theorem 3.15.
--
--   Differences from the source:
--   - generalization: T controlled phase-oracle queries, |S| = k → T queries each of which may be the controlled oracle or its controlled adjoint; any S ⊆ [n]; reason: the source's setting is the special case with no adjoint queries and |S| = k
--   - encoding: the purified state of the algorithm and its query register → the register ℂⁿ × Bool × P of an OracleCircuit with an arbitrary finite workspace P and an arbitrary unit initial state; reason: the same purification
--   - encoding: H^(1)_x, H^(1)_ref as sums of projectors |j⟩⟨j| → diagonal matrices in the computational basis; reason: same operators
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), proof of Theorem 3.15, Eq. (5), p.15 (PDF p.16), with the family H^(1) of p.14 (PDF p.15)

import Definitions.Def_GapAgnosticGS_phaseOracle
import Definitions.Def_GapAgnosticGS_OracleCircuit_unitary
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), proof of Theorem 3.15, Eq. (5), p.15 (PDF p.16), with the setting of p.14 (PDF p.15):
"fix S ⊆ [n] with |S| = k and, for x ∈ S, set H^(1)_x = −α|x⟩⟨x| + (−α + ∆_gs) Σ_{j∈S∖{x}} |j⟩⟨j|
+ α Σ_{j∉S} |j⟩⟨j| … H^(1)_ref = (−α + ∆_gs) Σ_{j∈S} |j⟩⟨j| + α Σ_{j∉S} |j⟩⟨j| … With τ = π/(4α)";
p.15: "|Ψ^x_{t+1}⟩ = V_t O_x |Ψ^x_t⟩ … Summing over x ∈ S and recursively applying the inequality
on T queries gives (Σ_{x∈S} ‖|Ψ^x_T⟩ − |Ψ^ref_T⟩‖²)^{1/2} ≤ (π∆_gs/(4α)) T, (5) where the last
inequality used the fact that the projectors Π_x, x ∈ S, are orthogonal and the initial states
|Ψ^x_0⟩ and |Ψ^ref_0⟩ are identical."

For `α > 0`, `∆ ∈ (0, 2α]`, any `S ⊆ [n]` and any `T`-query oracle circuit (oracle-free unitaries
`V_t`, controlled queries) started from one unit state, the final states for the oracles
`e^{iτH^(1)_x}` (`x ∈ S`) and `e^{iτH^(1)_ref}` satisfy (5).

**Formalization Note.** The circuit may also query the adjoint oracle (`circ.adj`); with only
forward queries it is the paper's setting. The purification of the algorithm is the circuit's
register `ℂⁿ × Bool × P` with an arbitrary finite workspace `P`. -/
theorem eq_5 {n : ℕ} (S : Finset (Fin n)) (α Δ : ℝ) (hα : 0 < α) (hΔ : 0 < Δ)
    (hΔα : Δ ≤ 2 * α) {P : Type} [Fintype P] [DecidableEq P] {T : ℕ}
    (circ : OracleCircuit (Fin n) P T) (ψ₀ : EuclideanSpace ℂ (Fin n × Bool × P))
    (hψ₀ : ‖ψ₀‖ = 1) :
    let H1 : Fin n → Matrix (Fin n) (Fin n) ℂ := fun x => Matrix.diagonal fun j =>
      if j = x then ((-α : ℝ) : ℂ) else if j ∈ S then ((-α + Δ : ℝ) : ℂ) else ((α : ℝ) : ℂ)
    let Href : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun j =>
      if j ∈ S then ((-α + Δ : ℝ) : ℂ) else ((α : ℝ) : ℂ)
    let Ψ : Matrix (Fin n) (Fin n) ℂ → EuclideanSpace ℂ (Fin n × Bool × P) := fun M =>
      act (circ.unitary (phaseOracle M α)) ψ₀
    Real.sqrt (∑ x ∈ S, ‖Ψ (H1 x) - Ψ Href‖ ^ 2) ≤ Real.pi * Δ / (4 * α) * T := by sorry

end GapAgnosticGS
