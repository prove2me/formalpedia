-- Prove2me | Theorems.Thm_GaussianGLOCC_standard_form
-- name    : GaussianGLOCC.standard_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:38.319653+00:00
-- url     : https://prove2.me/theorems/159b4e1a-1581-4a91-92f1-bd5fb8918b60
-- title:
--   Lemma 1: standard form of pure $n\times n$-mode Gaussian states
-- statement:
--   Let $\rho$ be a pure Gaussian state of $n\times n$ modes with covariance matrix $\gamma$. Then there are squeezing parameters
--
--   $$
--   r_1\ge r_2\ge\dots\ge r_n\ge 0
--   $$
--
--   and Gaussian unitaries $U_A$ on system $A$ and $U_B$ on system $B$ such that
--
--   1. $(U_A\otimes U_B)\rho(U_A\otimes U_B)^\dagger=\bigotimes_{k=1}^n|\psi_{r_k}\rangle\langle\psi_{r_k}|$, the tensor product of $n$ pure two-mode squeezed states, $A$-mode $k$ paired with $B$-mode $k$;
--   2. $(S_A\oplus S_B)\gamma(S_A\oplus S_B)^T=\gamma_r=\begin{pmatrix}c(r)&s(r)\\s(r)&c(r)\end{pmatrix}$, where $S_A$, $S_B$ are the symplectic matrices of $U_A$, $U_B$.
--
--   Every orbit of pure states under local Gaussian unitaries thus contains a product of $n$ TMSS; this reduces the main theorem to states in normal form.
--
--   Differences from the source:
--   - encoding: transformed by local unitary Gaussian operations into a tensor product of n TMSS → unitaryB U_B (unitaryA U_A ρ) = tmssProduct r (A-mode k paired with B-mode k), together with the CM clause (S_A ⊕ S_B)γ(S_A ⊕ S_B)ᵀ = normalForm r; reason: local unitaries can permute modes, so fixing the pairing restricts nothing; the CM clause follows from the state clause by eq. (5) and is kept to tie the CM-level squeezing vector to states
--   - encoding: pure Gaussian state of n × n modes with CM γ (eqs. (1)–(2), vacuum CM 𝟙) → IsPureGaussian ρ γ on DensityKernel (n + n), A = first n modes, B = last n modes (published GaussianWithCovariance plus a norm-one vector representative); reason: the published predicate's extra clauses (γ positive definite, finite mean energy) hold for every Gaussian state; the mode order is a layout choice
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Lemma 1, p.4

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_LocalSteps
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Renew46.P39 (AffineMultimodeGaussianUnitary)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, Lemma 1 (Standard form of pure
`n × n`-states), p.4: "Any pure Gaussian state ρ of n × n modes can be transformed by local
unitary Gaussian operations into a state which is a tensor product of n pure two-mode squeezed
states (TMSS) with squeezing parameters r1 ≥ . . . ≥ rn ≥ 0."

For every pure Gaussian state `ρ` of `n + n` modes with CM `γ` there are `r₁ ≥ … ≥ rₙ ≥ 0`
and local Gaussian unitaries `U_A`, `U_B` (each on `n` modes) such that
1. `(U_A ⊗ U_B) ρ (U_A ⊗ U_B)† = ⊗_k |ψ_{r_k}⟩⟨ψ_{r_k}|` (the TMSS product, A-mode `k` paired
   with B-mode `k`), and
2. `(S_A ⊕ S_B) γ (S_A ⊕ S_B)ᵀ = [[c(r), s(r)], [s(r), c(r)]]`, `S_A`, `S_B` the symplectic
   matrices of `U_A`, `U_B`.

**Formalization Note.** Clause 1 is the printed claim; clause 2 is the same fact at the level of
CMs, which is how the main theorem's "CM γ, characterized by squeezing vector r" is read. The
order is descending (`Antitone`) as printed here; p.4 then uses the ascending order. Local
unitaries include displacements, so the TMSS product is centered. -/
theorem standard_form (n : ℕ) (ρ : DensityKernel (n + n)) (γ : Cov (n + n))
    (hρ : IsPureGaussian ρ γ) :
    ∃ r : Fin n → ℝ, Antitone r ∧ (∀ k, 0 ≤ r k) ∧
      ∃ UA UB : AffineMultimodeGaussianUnitary n,
        unitaryB UB (unitaryA UA ρ) = tmssProduct r ∧
        localSymplectic UA.symplecticMatrix UB.symplecticMatrix * γ *
            (localSymplectic UA.symplecticMatrix UB.symplecticMatrix).transpose = normalForm r := by sorry

end GaussianGLOCC
