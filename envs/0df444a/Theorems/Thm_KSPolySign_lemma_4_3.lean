-- Prove2me | Theorems.Thm_KSPolySign_lemma_4_3
-- name    : KSPolySign.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:34:03.466198+00:00
-- url     : https://prove2.me/theorems/18dd1b96-dec5-4a53-a2c7-bf57097eb3fa
-- title:
--   Lemma 4.3 — variance and signing stability
-- statement:
--   Let $A_1,\dots,A_m$ ($m\ge1$) be nonzero Hermitian rank-one matrices with eigenvalue signs $\varepsilon_i$; put $B_i=\varepsilon_iA_i$, $a_*=\max_{i,j}(B_i)_{jj}$, choose $a_*\le D_{\mathrm{aux}}<2a_*$, and let $\bar A_i=B_i/D_{\mathrm{aux}}$, $\zeta_0=\|\sum_i\bar A_i^2\|$ (Lemma 4.1). Let $\xi=10^{-8}$, $\delta=\xi/(mn)$, and let $\tilde A_i$ satisfy $\|\tilde A_i-\bar A_i\|_F\le\delta$ (Lemma 4.2). Put $\tilde\zeta=\|\sum_i\tilde A_i^2\|$ and $C_*=3.4813833$.
--
--   1. $|\tilde\zeta-\zeta_0|\le3\xi$ and $\sqrt{\tilde\zeta}\le(1+6\xi)\sqrt{\zeta_0}$.
--   2. If $\tau\in\{-1,1\}^m$ satisfies $\|\sum_i\tau_i\tilde A_i\|\le C_*\sqrt{\tilde\zeta}$, then $\sigma_i=\varepsilon_i\tau_i$ satisfies
--   $$\Big\|\sum_i\sigma_iA_i\Big\|<3.4814\sqrt{\Big\|\sum_iA_i^2\Big\|}.$$
--
--   A signing of the rounded inputs therefore transfers to the original inputs within the final constant.
--
--   **Formalization Note** $\varepsilon_i$ is the sign of the (real, nonzero) trace; $a_*$ is given by its defining property.
--
--   Differences from the source:
--   - generalization: the dyadic rank-one approximations Ã_i of Lemma 4.2 → any matrices Ã_i with ‖Ã_i − Ā_i‖_F ≤ δ; reason: the proof (pp.35–36) uses only Lemma 4.2(a)'s Frobenius bound; Lemma 4.2's approximations are among them
--   - encoding: ε_i the eigenvalue sign; a_* = max_{i,j}(B_i)_jj → ε_i = 1 if re tr A_i > 0 else −1; a_* an attained upper bound of the real diagonal entries; reason: same values
--   - encoding: operator norm ‖·‖ induced by the Euclidean norm; ‖X‖^{1/2} → AgnosticTNS.opNorm (sup of ‖Xv‖ over the Euclidean unit ball); Real.sqrt; reason: Lean convention; same values
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.3, p.35 (PDF p.35); setting of Lemma 4.1, p.32 and Lemma 4.2, p.33

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 4.3 (Variance and signing stability).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 4.3, p.35 (PDF p.35), in the setting
of Lemma 4.1, p.32 (PDF p.32) and Lemma 4.2, p.33 (PDF p.33).

For nonzero Hermitian rank-one `A_1, …, A_m` (`m ≥ 1`) with eigenvalue signs `ε_i`, `B_i = ε_iA_i`,
`a_* = max_{i,j} (B_i)_{jj}`, `a_* ≤ D_aux < 2a_*`, `Ā_i = B_i/D_aux`, `ζ₀ = ‖∑ Ā_i²‖`, `ξ = 10⁻⁸`,
`δ = ξ/(mn)`, and approximations `Ã_i` with `‖Ã_i − Ā_i‖_F ≤ δ`, put `ζ̃ = ‖∑ Ã_i²‖`, `C_* = 3.4813833`.
(a) `|ζ̃ − ζ₀| ≤ 3ξ` and `√ζ̃ ≤ (1 + 6ξ)√ζ₀`. (b) If `τ ∈ {±1}^m` has `‖∑ τ_iÃ_i‖ ≤ C_*√ζ̃`, then
`σ_i = ε_iτ_i` gives `‖∑ σ_iA_i‖ < 3.4814√‖∑ A_i²‖`.

**Formalization Note** `ε_i` is the sign of the (real, nonzero) trace, as in Lemma 3.1. `a_*` is given
by its defining property (an upper bound of the real diagonal entries of the `B_i` that is attained).
The `Ã_i` are any matrices within Frobenius distance `δ` of the `Ā_i` (the rank-one dyadic
approximations of Lemma 4.2 are among them). `‖·‖` is the Euclidean operator norm (`AgnosticTNS.opNorm`, published); `‖X‖^{1/2}` is `Real.sqrt`. -/
theorem lemma_4_3 (m n : ℕ) (hm : 1 ≤ m) (A : Fin m → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i, (A i).IsHermitian ∧ (A i).rank = 1) :
    let ε : Fin m → ℝ := fun i => if 0 < (A i).trace.re then 1 else -1
    let B : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((ε i : ℝ) : ℂ) • A i
    ∀ aStar : ℝ, (∀ i j, (B i j j).re ≤ aStar) → (∃ i j, (B i j j).re = aStar) →
    ∀ Daux : ℝ, aStar ≤ Daux → Daux < 2 * aStar →
    let Abar : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => ((1 / Daux : ℝ) : ℂ) • B i
    let ζ0 : ℝ := AgnosticTNS.opNorm (∑ i, Abar i * Abar i)
    let ξ : ℝ := 1 / 10 ^ 8
    let δ : ℝ := ξ / ((m : ℝ) * n)
    ∀ Atil : Fin m → Matrix (Fin n) (Fin n) ℂ, (∀ i, Real.sqrt (∑ j, ∑ l, ‖(Atil i - Abar i) j l‖ ^ 2) ≤ δ) →
      let ζt : ℝ := AgnosticTNS.opNorm (∑ i, Atil i * Atil i)
      let Cstar : ℝ := 3.4813833
      (|ζt - ζ0| ≤ 3 * ξ ∧ Real.sqrt ζt ≤ (1 + 6 * ξ) * Real.sqrt ζ0) ∧
        ∀ τ : Fin m → ℝ, (∀ i, τ i = 1 ∨ τ i = -1) →
          AgnosticTNS.opNorm (∑ i, ((τ i : ℝ) : ℂ) • Atil i) ≤ Cstar * Real.sqrt ζt →
          AgnosticTNS.opNorm (∑ i, ((ε i * τ i : ℝ) : ℂ) • A i) <
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i)) := by sorry

end KSPolySign
