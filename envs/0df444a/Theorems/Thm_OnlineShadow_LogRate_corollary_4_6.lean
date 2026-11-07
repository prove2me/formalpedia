-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_corollary_4_6
-- name    : OnlineShadow.LogRate.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:11:01.754189+00:00
-- url     : https://prove2.me/theorems/661301a2-c361-4b62-9ece-fe15da765709
-- title:
--   Corollary 4.6 — a soft measurement raises the energy by at most $\frac{2\lambda^2}{n^2}\mathrm{Tr}(F\tau)$
-- statement:
--   Let $\mathcal H=\mathbb C^d$, let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ ($\mathcal R=\mathbb C^r$) purifying the state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and let $A$ be a single-copy observable with $0\preceq A\preceq1$. On $(\mathcal H\otimes\mathcal R)^{\otimes n}$ let $\overline A$ denote the lift of $A\otimes1_{\mathcal R}$, $\overline X=\overline A-\mathrm{Tr}(A\rho)1$, $\mathsf N$ the number operator and $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$ the energy relative to $\psi$.
--
--   Let $b\in\mathbb R$, $0<\lambda\le n$, and $F=f_{b,\lambda}(\overline A)$ with $f_{b,\lambda}(x)=1/(1+e^{\lambda(b-x)})$. For a positive semidefinite $\tau$ let $\Phi_F(\tau)=\sqrt F\tau\sqrt F+\sqrt{1-F}\tau\sqrt{1-F}$ be the expected post-measurement state.
--
--   **Corollary 4.6.**
--   $$\mathcal E[\Phi_F(\tau)]-\mathcal E[\tau]\le\frac{2\lambda^2}{n^2}\,\mathrm{Tr}(F\tau).$$
--
--   Summed over the protocol's tree, this bounds the total energy by $2\lambda^2K/n^2$, since the expected number of flags is at most $K$.
--
--   **Formalization Note** Traces are real parts.
--
--   Differences from the source:
--   - generalization: τ an arbitrary mixed state → τ any positive semidefinite operator; reason: the claim is linear in τ; mixed states are a special case (paper.md R12)
--   - encoding: $|\psi\rangle$ any purification of $\rho$ on $\mathcal H\otimes\mathcal R$ → ψ : Fin d × Fin r → ℂ with ∑ₓ ‖ψ x‖² = 1 for any r, and ρ := Tr_R |ψ⟩⟨ψ| (marginal ψ); reason: the same objects: every purification is a unit vector on ℂ^d ⊗ ℂ^r and every ρ has one with r = d (paper.md R12)
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Corollary 4.6, p. 13 (proof p. 17)

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_liftObs
import Definitions.Def_OnlineShadow_LogRate_energy
import Definitions.Def_OnlineShadow_LogRate_logistic
import Definitions.Def_OnlineShadow_LogRate_measChannel

open scoped Kronecker ComplexOrder

namespace OnlineShadow.LogRate

/-- **Corollary 4.6** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.13; proof p.17). Let `ψ` be a unit vector on `H ⊗ R`, `A` an effect on
`H`, `b` real, `0 < λ ≤ n`, and `F = f_{b,λ}(Ā ⊗ 1_R)` with `f_{b,λ}(x) = 1/(1 + e^{λ(b − x)})`. For
every positive semidefinite `τ` on `(H ⊗ R)^{⊗n}` and `Φ_F(τ) = √F τ √F + √(1 − F) τ √(1 − F)`,
`E[Φ_F(τ)] − E[τ] ≤ (2λ²/n²) Tr(Fτ)`.

**Formalization Note** The paper's "arbitrary mixed state" is generalized to any positive semidefinite
`τ` (linear claim; paper.md R12). `0 < λ ≤ n` forces `n ≥ 1`. Traces are real parts. -/
theorem corollary_4_6 {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) (n : ℕ)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : ShadowTomography.UpperBound.IsEffect A)
    (b lam : ℝ) (hlam : 0 < lam) (hlamn : lam ≤ n)
    (τ : Matrix (Fin n → Fin d × Fin r) (Fin n → Fin d × Fin r) ℂ) (hτ : τ.PosSemidef) :
    let F := cfc (logistic b lam) (liftObs n (A ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ)))
    energy ψ n (measChannel F τ) - energy ψ n τ ≤ 2 * lam ^ 2 / (n : ℝ) ^ 2 * (F * τ).trace.re := by sorry

end OnlineShadow.LogRate
