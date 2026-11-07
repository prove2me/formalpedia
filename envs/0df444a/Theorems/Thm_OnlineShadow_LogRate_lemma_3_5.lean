-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_lemma_3_5
-- name    : OnlineShadow.LogRate.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:10:50.815494+00:00
-- url     : https://prove2.me/theorems/fdbf8c39-1ac4-4e42-a1b7-92fb18f2776b
-- title:
--   Lemma 3.5 — $\overline X^2\preceq\frac9n(\mathsf N+1)$
-- statement:
--   Let $\mathcal H=\mathbb C^d$, let $\psi$ be a unit vector on $\mathcal H\otimes\mathcal R$ ($\mathcal R=\mathbb C^r$) purifying the state $\rho=\mathrm{Tr}_{\mathcal R}|\psi\rangle\langle\psi|$, and let $A$ be a single-copy observable with $0\preceq A\preceq1$. On $(\mathcal H\otimes\mathcal R)^{\otimes n}$ let $\overline A$ denote the lift of $A\otimes1_{\mathcal R}$, $\overline X=\overline A-\mathrm{Tr}(A\rho)1$, $\mathsf N$ the number operator and $\mathcal E[\tau]=\frac1n\mathrm{Tr}(\mathsf N\tau)$ the energy relative to $\psi$.
--
--   **Lemma 3.5.** For every $n\ge1$,
--   $$\overline X^{\,2}\preceq\frac9n(\mathsf N+1).$$
--
--   The fluctuation of the empirical average around the true mean is controlled by the number of excited copies: on unexcited copies it is of order $1/n$. This is the operator inequality behind Lemma 3.4.
--
--   **Formalization Note** The Loewner order $X\preceq Y$ is positive semidefiniteness of $Y-X$.
--
--   Differences from the source:
--   - encoding: any number of copies n → n ≥ 1; reason: 9/n is undefined at n = 0
--   - reading: μ in X = (A − μ1) ⊗ 1_R, not defined on the page → μ = Tr(Aρ); reason: the display PXP = (Tr(Aρ) − μ)P = 0 on p. 9 forces it (paper.md R6)
--   - encoding: $|\psi\rangle$ any purification of $\rho$ on $\mathcal H\otimes\mathcal R$ → ψ : Fin d × Fin r → ℂ with ∑ₓ ‖ψ x‖² = 1 for any r, and ρ := Tr_R |ψ⟩⟨ψ| (marginal ψ); reason: the same objects: every purification is a unit vector on ℂ^d ⊗ ℂ^r and every ρ has one with r = d (paper.md R12)
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Lemma 3.5, p. 9

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_OnlineShadow_LogRate_Xbar
import Definitions.Def_OnlineShadow_LogRate_numberOp

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Lemma 3.5** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.9). Let `ψ` be a unit vector on `H ⊗ R` (`H = ℂ^d`, `R = ℂ^r`), purifying
`ρ = Tr_R |ψ⟩⟨ψ|`, let `A` be an effect on `H` and `n ≥ 1`. With `X̄ = Ā ⊗ 1_R − Tr(Aρ)1` and the
number operator `N` on `(H ⊗ R)^{⊗n}`, `X̄² ⪯ (9/n)(N + 1)`.

**Formalization Note** Loewner order `X ⪯ Y` is `(Y − X).PosSemidef`. `n ≥ 1` because `9/n` is
undefined at `n = 0` (paper.md R6 fixes `μ = Tr(Aρ)`). -/
theorem lemma_3_5 {d r : ℕ} (ψ : Fin d × Fin r → ℂ) (hψ : ∑ x, ‖ψ x‖ ^ 2 = 1) (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : ShadowTomography.UpperBound.IsEffect A) :
    ((((9 : ℝ) / n : ℝ) : ℂ) • (numberOp ψ n + 1) - Xbar ψ n A * Xbar ψ n A).PosSemidef := by sorry

end OnlineShadow.LogRate
