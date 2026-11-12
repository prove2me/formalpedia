-- Prove2me | Theorems.Thm_ImpuritySim_theorem_4_1
-- name    : ImpuritySim.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:41.586442+00:00
-- url     : https://prove2.me/theorems/947d71ba-5690-44c0-b80b-a5b7b0823f27
-- title:
--   Theorem 4.1 — $\mathrm{Tr}((I-P_S)\rho)\le\delta^2/4$ and $\dim\mathcal H_S\le\exp[O(m\log\frac{2J}\omega+\log\delta^{-1}+\log\mathrm{Tr}(\rho e^{D/2}))]$, $S$ enumerable in time $O(n|S|)$
-- statement:
--   Let $\rho$ be a state of a Hamiltonian in the form (3.15) on $n$ modes and suppose the weights satisfy (4.2) and $h_d\ge\min\{d-1,\tau\}$ with $\tau=\max\{1,\frac18\log n\}$. For $0<\delta<1$ let
--   $$S=\{x:D(x)\le T\},\qquad T=4\log(2\delta^{-1})+2\log\operatorname{Tr}\bigl(\rho e^{D/2}\bigr),\qquad(4.6)$$
--   $\mathcal H_S=\operatorname{span}\{|x\rangle:x\in S\}$ and $P_S$ its projector. Then
--
--   1. $\operatorname{Tr}((I-P_S)\rho)\le\delta^2/4$;
--   2. $$\dim\mathcal H_S\le\exp\Bigl[O\Bigl(m\log\frac{2J}\omega+\log\delta^{-1}+\log\operatorname{Tr}\bigl(\rho e^{D/2}\bigr)\Bigr)\Bigr];\qquad(4.7)$$
--   3. $S$ can be enumerated in time $O(n|S|)$ by a classical algorithm;
--   4. $D(x)$ involves only residual-bath occupations, so $P_S$ acts trivially on the enlarged-impurity modes.
--
--   This is the compression lemma: a bound on the exponential moment of the weighted occupation gives a small subspace carrying almost all of $\rho$.
--
--   **Formalization Note** The $O(\cdot)$ constant $C$ is absolute: it is chosen before $n$, the form, the weights, $\rho$ and $\delta$. The enumerator is one admissible deterministic real-RAM program listing every threshold set $\{x:\sum_iw_ix_i\le T\}$ ($w\ge0$, $T\ge0$) within $C'\,n\,|S|$ steps; $S$ is the threshold set of the weights $h_{d(i)}$ on bath modes and $0$ elsewhere. $\dim\mathcal H_S=|S|$.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - reading: "the set S can be enumerated in time O(n|S|) by a classical algorithm" → one Admissible, Deterministic program of the published unit-cost real RAM lists every threshold set {x : Σ_i w_i x_i ≤ T} (w ≥ 0, T ≥ 0) within C'·n·|S| steps, leaving |S| and the elements of S in integer memory (EnumeratesThresholdSets); reason: the paper names no machine; App. B.1's algorithm runs on this real RAM; one program for every threshold set is the stronger reading
--   - encoding: "P_S acts trivially on the enlarged-impurity modes" → x ∈ S ↔ x' ∈ S whenever x and x' agree on all bath modes; reason: P_S is diagonal in the Fock basis; acting as identity on the enlarged-impurity factor is exactly this
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 4.1, Eqs. (4.6)–(4.7), p.20; proof p.21 and App. B.1, pp.54–55

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Theorem 4.1 (Exponential moment to size of support)**, p.20, of J. Jiang, N. Ju, O. Parekh,
C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eqs. (4.6)–(4.7).

Suppose `h_d ≥ min{d − 1, τ}` with `τ = max{1, (1/8) log n}`. For any `0 < δ < 1` let
`S = {x : D(x) ≤ T}` with `T = 4 log(2δ⁻¹) + 2 log Tr(ρ e^{D/2})` (4.6), `H_S = span{|x⟩ : x ∈ S}`
and `P_S` its projector. Then
1. `Tr((I − P_S) ρ) ≤ δ²/4`;
2. `dim H_S ≤ exp[O(m log(2J/ω) + log δ⁻¹ + log Tr(ρ e^{D/2}))]` (4.7);
3. `S` can be enumerated in time `O(n|S|)` by a classical algorithm;
4. `P_S` acts trivially on the enlarged-impurity modes: membership in `S` depends only on the
   residual-bath bits.

**Formalization Note.**
* The constant of `O(·)` is one absolute `C`, chosen before `n`, the form `F`, `h`, `ρ` and `δ`.
* "Enumerated in time `O(n|S|)` by a classical algorithm": one `Admissible`, `Deterministic` program
  of the published unit-cost real RAM lists every threshold set `{x : Σ_i w_i x_i ≤ T}` (`w ≥ 0`,
  `T ≥ 0`) within `C'·n·|S|` steps (`EnumeratesThresholdSets`); `S` is the threshold set of the
  weights `h_{d(i)}` on bath modes and `0` elsewhere (`thresholdSet`).
* `ρ` is a density matrix and `h` satisfies (4.2) (standing assumptions of §4); `λ = 1/4`, so
  `e^{2λD} = e^{D/2}` (`expHalfD`); `log` is the natural logarithm. `dim H_S = |S|`. -/
theorem theorem_4_1 :
    ∃ C : ℝ,
      (∃ (P : SubsetConvFPRAS.Program) (C' : ℕ), SubsetConvFPRAS.Admissible P ∧
        SYKCavity.Deterministic P ∧ EnumeratesThresholdSets P C') ∧
      ∀ (n : ℕ) (F : BandwiseForm n) (h : ℕ → ℝ), ValidWeights h →
        (∀ d : ℕ, 1 ≤ d → min ((d : ℝ) - 1) (max 1 (Real.log n / 8)) ≤ h d) →
        ∀ ρ : FermiCap.Gaussian.Op n, IsDensity ρ → ∀ δ : ℝ, 0 < δ → δ < 1 →
          let T := 4 * Real.log (2 * δ⁻¹) + 2 * Real.log (ρ * F.expHalfD h).trace.re
          let S := F.thresholdSet h T
          ((1 - projS S) * ρ).trace.re ≤ δ ^ 2 / 4 ∧
          (S.card : ℝ) ≤ Real.exp (C * ((F.m : ℝ) * Real.log (2 * F.J / F.ω) + Real.log δ⁻¹ +
            Real.log (ρ * F.expHalfD h).trace.re)) ∧
          ∀ x x' : FermiCap.Gaussian.Qubits n, (∀ i ∈ F.bath, x i = x' i) → (x ∈ S ↔ x' ∈ S) := by sorry

end ImpuritySim
