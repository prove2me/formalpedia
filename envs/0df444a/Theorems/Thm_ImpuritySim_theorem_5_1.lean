-- Prove2me | Theorems.Thm_ImpuritySim_theorem_5_1
-- name    : ImpuritySim.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:36:18.479415+00:00
-- url     : https://prove2.me/theorems/eb8b55c1-c2ca-4888-a560-a768ba4e66d4
-- title:
--   Theorem 5.1 — $\mathrm{Tr}(\rho^{(\infty)}e^{D^{(\infty)}/2})\le e^{4\kappa}$, $\kappa\le8m(L+1)$, and $\mathrm{Tr}(\rho^{(\infty)}n_i)\le32\sqrt e\,m\,e^{-d(i)/2}$
-- statement:
--   Let $\rho^{(\infty)}$ be a ground state of a Hamiltonian $H$ in the form (3.15), and let $D^{(\infty)}=\sum_i(d(i)-1)n_i$ (5.1). Then
--
--   1. $$\operatorname{Tr}\bigl(\rho^{(\infty)}e^{\frac12D^{(\infty)}}\bigr)\le\exp(4\kappa);\qquad(5.3)$$
--   2. $\kappa=O(m\log_2(J/\omega))$ as in (3.17), namely $\kappa\le8m(L+1)=8m\bigl(1+\lceil\log_2(J/\omega)\rceil\bigr)$;
--   3. residual-bath occupation decays exponentially with Krylov depth: for every residual-bath mode $i$,
--   $$\operatorname{Tr}\bigl(\rho^{(\infty)}n_i\bigr)\le32\sqrt e\,m\,e^{-d(i)/2}.\qquad(5.4)$$
--
--   The exponential moment bound is what Theorem 4.1 converts into a polynomial-size support for the ground state.
--
--   **Formalization Note** A ground state is any density matrix $\rho$ with $H\rho=\lambda_{\min}(H)\rho$.
--
--   Differences from the source:
--   - generalization: an impurity Hamiltonian in the bandwise hybridization form (3.15), built from (1.1) by App. A and §3 → any BandwiseForm: any data on n modes with the properties (3.15)–(3.18) and Lemma 3.1 record (bath set, bands ≤ L, depths ≥ 1, shell sizes ≤ 2m, impurity size ≤ m + 2m(L+1), E Hermitian, band-diagonal and depth-tridiagonal with ω_ℓ I ≤ E_ℓ ≤ 2ω_ℓ I, orthonormal u_ℓs in the depth-1 shell, ‖G_ℓs‖ ≤ 2ω_ℓ, K even on the enlarged impurity); reason: every form produced by the paper's construction has these properties, so the statement specializes to the paper's; the proofs use only these properties
--   - generalization: "a ground state ρ^(∞)" → every density matrix ρ with Hρ = λ_min(H) ρ (pure or mixed); reason: contains the pure ground states; the proof uses only Δ_I ≥ 0 (5.2), which holds for every such ρ
--   - reading: "κ = O(m log₂(J/ω)) as in Eq. (3.17)" → κ ≤ 8m(L + 1); reason: (3.17) states this explicit bound
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), Theorem 5.1, Eqs. (5.3)–(5.4), p.26; (5.1), p.26; (3.17), p.18; proof App. B.3, pp.56–57

import Mathlib
import Definitions.Def_ImpuritySim_Occupation

open Matrix

namespace ImpuritySim

/-- **Theorem 5.1 (Exponential localization of residual-bath occupation in Krylov depth)**, p.26,
of J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum
simulation of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2),
Eqs. (5.3)–(5.4), with (5.1) and (3.17).

Let `ρ^(∞)` be a ground state of an impurity Hamiltonian `H` in the form (3.15). Then
1. `Tr(ρ^(∞) e^{D^(∞)/2}) ≤ exp(4κ)`, where `D^(∞) = Σ_i (d(i) − 1) n_i` (5.1), (5.3);
2. `κ = O(m log₂(J/ω))` as in (3.17), i.e. `κ ≤ 8m(L + 1)`;
3. for every residual-bath mode `i`, `Tr(ρ^(∞) n_i) ≤ 32√e · m · e^{−d(i)/2}` (5.4).

**Formalization Note.** "Ground state" is any density matrix `ρ` with `Hρ = λ_min(H) ρ`
(`IsGroundState`), pure or mixed. The weights are `h^(∞)_d = d − 1` (`hInf`). The `O(·)` of (5.3)
is the explicit bound `κ ≤ 8m(1 + ⌈log₂(J/ω)⌉)` of (3.17). -/
theorem theorem_5_1 {n : ℕ} (F : BandwiseForm n) (ρ : FermiCap.Gaussian.Op n)
    (hρ : IsGroundState F.H ρ) :
    (ρ * F.expHalfD hInf).trace.re ≤ Real.exp (4 * F.kappa) ∧
      F.kappa ≤ 8 * (F.m : ℝ) * ((F.L : ℝ) + 1) ∧
      ∀ i ∈ F.bath, (ρ * FermiHubbardMix.numOp n i).trace.re ≤
        32 * Real.sqrt (Real.exp 1) * (F.m : ℝ) * Real.exp (-(F.depth i : ℝ) / 2) := by sorry

end ImpuritySim
