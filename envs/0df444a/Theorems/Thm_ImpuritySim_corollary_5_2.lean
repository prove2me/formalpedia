-- Prove2me | Theorems.Thm_ImpuritySim_corollary_5_2
-- name    : ImpuritySim.corollary_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:20.977296+00:00
-- url     : https://prove2.me/theorems/0c81deae-37f7-4685-94d6-8d438ee306e5
-- title:
--   Corollary 5.2 — compression of the ground state: $\dim\mathcal H_S\le\mathrm{poly}(n,\delta^{-1},J,\omega^{-1})$, $\mathrm{Tr}((I-P_S)\rho^{(\infty)})\le\delta^2/4$, energy error $\le\|H\|\delta$
-- statement:
--   Let $H$ be in the form (3.15) with impurity size $m$. For every $0<\delta<1$ there is an efficiently enumerable set $S$ of Fock configurations such that, with $\mathcal H_S=\operatorname{span}\{|x\rangle:x\in S\}$ and $P_S$ its projector,
--
--   1. $\dim\mathcal H_S\le\mathrm{poly}(n,\delta^{-1},J,\omega^{-1})$;
--   2. $\operatorname{Tr}\bigl((I-P_S)\rho^{(\infty)}\bigr)\le\delta^2/4$ for every ground state $\rho^{(\infty)}$ of $H$; (5.6)
--   3. the ground energy of $P_SHP_S$ restricted to $\mathcal H_S$ differs from the ground energy of $H$ by at most $\|H\|\delta$:
--   $$\bigl|\lambda_{\min}(H_S)-\lambda_{\min}(H)\bigr|\le\|H\|\,\delta,\qquad (H_S)_{x,y}=\langle x|H|y\rangle,\ x,y\in S.$$
--
--   Here "poly" means: for each $m\ge1$ there are constants $C,K$ with $|S|\le C(n+\delta^{-1}+J+\omega^{-1})^K$. The ground-state energy problem is thereby reduced to a Hermitian eigenvalue problem of polynomial size.
--
--   **Formalization Note** "Efficiently enumerable": $S=\{x:D^{(\infty)}(x)\le T\}$ is a threshold set of the depth weights $h^{(\infty)}_d=d-1$ for some $T\ge0$, and one fixed admissible deterministic real-RAM program lists every such threshold set in $C'\,n\,|S|$ steps. $\|H\|$ is the spectral norm; ground states are pure or mixed.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - generalization: "Let ρ^(∞) be any ground state … there exists … S" (S may depend on ρ^(∞)) → one S (one threshold T) chosen before the state serves every ground state, pure or mixed (IsGroundState); reason: implies the per-state statement; Theorem 5.1's bound is uniform over ground states, so T = 4 log(2/δ) + 8κ works for all
--   - reading: "an efficiently enumerable subset S" → S = {x : D^(∞)(x) ≤ T} for some T ≥ 0, plus one fixed Admissible, Deterministic real-RAM program listing every threshold set in C'·n·|S| steps (EnumeratesThresholdSets); reason: the paper's S is this threshold set (proof via Theorem 4.1); the enumerator is Theorem 4.1's
--   - encoding: dim(H_S) ≤ poly(n, δ^{−1}, J, ω^{−1}), m = O(1) → ∀ m ≥ 1, ∃ C K : ℕ, |S| ≤ C·(n + δ^{−1} + J + ω^{−1})^K; reason: the polynomial may depend on the constant m
--   - encoding: "the ground energy of P_S H P_S, when restricted to H_S" → groundEnergy (restrictTo H S), the least eigenvalue of the submatrix (⟨x|H|y⟩)_{x,y∈S}; reason: the same matrix (as on p.27)
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Corollary 5.2, Eq. (5.6), p.26; proof p.27

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Corollary 5.2 (Compression of the ground state)**, p.26, of J. Jiang, N. Ju, O. Parekh,
C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation of quantum impurity models*,
arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Eq. (5.6).

Let `ρ^(∞)` be any ground state of an impurity Hamiltonian `H` in the form (3.15). For every
`0 < δ < 1` there is an efficiently enumerable set `S` of Fock configurations such that
`H_S = span{|x⟩ : x ∈ S}` has `dim H_S ≤ poly(n, δ⁻¹, J, ω⁻¹)` and `Tr((I − P_S) ρ^(∞)) ≤ δ²/4`;
moreover the ground energy of `P_S H P_S` restricted to `H_S` differs from that of `H` by at most
`‖H‖δ`.

**Formalization Note.**
* `poly(·)`: for each impurity size `m ≥ 1` there are `C, K` with `|S| ≤ C (n + δ⁻¹ + J + ω⁻¹)^K`.
* "Efficiently enumerable": `S = {x : D^(∞)(x) ≤ T}` is a threshold set of the depth weights
  `h^(∞)_d = d − 1` for some `T ≥ 0`, and one fixed `Admissible`, `Deterministic` real-RAM program
  lists every such threshold set in `C'·n·|S|` steps (`EnumeratesThresholdSets`).
* `S` is chosen before the ground state: one `S` serves every ground state `ρ` (pure or mixed,
  `IsGroundState`); this implies the per-state statement.
* The restriction is `(H_S)_{x,y} = ⟨x|H|y⟩`, `x, y ∈ S` (`restrictTo`); ground energies are
  `λ_min` (`groundEnergy`); `‖H‖` is the spectral norm. -/
theorem corollary_5_2 :
    (∃ (P : SubsetConvFPRAS.Program) (C' : ℕ), SubsetConvFPRAS.Admissible P ∧
        SYKCavity.Deterministic P ∧ EnumeratesThresholdSets P C') ∧
      ∀ m : ℕ, 1 ≤ m → ∃ C K : ℕ, ∀ (n : ℕ) (F : BandwiseForm n), F.m = m →
        ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ T : ℝ, 0 ≤ T ∧
          let S := F.thresholdSet hInf T
          (S.card : ℝ) ≤ (C : ℝ) * ((n : ℝ) + δ⁻¹ + F.J + F.ω⁻¹) ^ K ∧
          (∀ ρ : FermiCap.Gaussian.Op n, IsGroundState F.H ρ →
            ((1 - projS S) * ρ).trace.re ≤ δ ^ 2 / 4) ∧
          |groundEnergy (restrictTo F.H S) - groundEnergy F.H| ≤ specNorm F.H * δ := by sorry

end ImpuritySim
