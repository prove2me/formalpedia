-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_3_4
-- name    : OnlineShadow.LogRate.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:11:52.458464+00:00
-- url     : https://prove2.me/theorems/ebccc9e6-6156-4812-a283-03c937ea9609
-- title:
--   Lemma 3.4 — energy bounds the probability of a large deviation
-- statement:
--   Let $\mathcal H=\mathbb C^d$, let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ ($\mathcal R=\mathbb C^r$) purifying the state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and let $A$ be a single-copy observable with $0\preceq A\preceq1$. On $(\mathcal H\otimes\mathcal R)^{\otimes n}$ let $\overline A$ denote the lift of $A\otimes1_{\mathcal R}$, $\overline X=\overline A-\mathrm{Tr}(A\rho)1$, $\mathsf N$ the number operator and $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$ the energy relative to $\psi$.
--
--   **Lemma 3.4.** Let $\xi>0$ satisfy $n\xi^2\ge18$, let $\tau$ be a positive semidefinite operator on $(\mathcal H\otimes\mathcal R)^{\otimes n}$, and let $B=\mathbf 1_{|\overline A-\mathrm{Tr}(A\rho)1|\ge\xi}$ be the projector onto the event that the lifted observable deviates from $\mathrm{Tr}(A\rho)$ by at least $\xi$. Then
--   $$\mathrm{Tr}(B\tau)\le\frac9{\xi^2}\,\mathcal E[\tau]+\frac12\mathrm{Tr}(\tau).$$
--   As a consequence, if $\tau$ lies in the subspace of $B$ (that is, $B\tau B=\tau$), then
--   $$\mathrm{Tr}(\tau)\le\frac{18}{\xi^2}\,\mathcal E[\tau].$$
--
--   A state that the measurement of the lifted observable would report far from the truth must carry energy; this converts every wrong answer into energy.
--
--   **Formalization Note** Traces are real parts.
--
--   Differences from the source:
--   - generalization: τ a sub-normalized mixed state → τ any positive semidefinite operator; reason: both claims are linear in τ; sub-normalized states are a special case (paper.md R12)
--   - reading: τ lies in the subspace corresponding to B → BτB = τ; reason: for positive semidefinite τ this is equivalent to range τ ⊆ range B
--   - encoding: $|\psi\rangle$ any purification of $\rho$ on $\mathcal H\otimes\mathcal R$ → ψ : Fin d × Fin r → ℂ with ∑ₓ ‖ψ x‖² = 1 for any r, and ρ := Tr_R |ψ⟩⟨ψ| (marginal ψ); reason: the same objects: every purification is a unit vector on ℂ^d ⊗ ℂ^r and every ρ has one with r = d (paper.md R12)
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 3.4, p. 9

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_spectralInd
import Definitions.Def_OnlineShadow_LogRate_energy

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 3.4** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.9). Let `ψ` be a unit vector on `H ⊗ R` purifying `ρ = Tr_R |ψ⟩⟨ψ|`, `A` an
effect on `H`, `ξ > 0` with `n ξ² ≥ 18`, `τ` a positive semidefinite operator on `(H ⊗ R)^{⊗n}`, and
`B = 1_{|Ā − Tr(Aρ)1| ≥ ξ}`. Then `Tr(Bτ) ≤ (9/ξ²) E[τ] + (1/2) Tr(τ)`; and if `τ` lies in the subspace
of `B` (`BτB = τ`), then `Tr(τ) ≤ (18/ξ²) E[τ]`.

**Formalization Note** The paper's "sub-normalized mixed state" is generalized to any positive
semidefinite `τ` (the claims are linear; paper.md R12). "`τ` lies in the subspace corresponding to `B`"
is `B τ B = τ`, which for positive semidefinite `τ` is equivalent to `range τ ⊆ range B`. Traces are
real parts. -/
theorem lemma_3_4 {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) (n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : ShadowTomography.UpperBound.IsEffect A)
    (ξ : ℝ) (hξ : 0 < ξ) (hnξ : 18 ≤ (n : ℝ) * ξ ^ 2)
    (τ : Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ) (hτ : τ.PosSemidef) :
    (spectralInd ψ n A ξ * τ).trace.re ≤ 9 / ξ ^ 2 * energy ψ n τ + 1 / 2 * τ.trace.re ∧
      (spectralInd ψ n A ξ * τ * spectralInd ψ n A ξ = τ →
        τ.trace.re ≤ 18 / ξ ^ 2 * energy ψ n τ) := by sorry

end OnlineShadow.LogRate
