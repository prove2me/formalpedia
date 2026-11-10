-- Prove2me | Theorems.Thm_KnownFidelity_Rank_lemma_4_2
-- name    : KnownFidelity.Rank.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:49:20.913082+00:00
-- url     : https://prove2.me/theorems/6594d6f5-e266-40c9-85b0-2cfa512d98f7
-- title:
--   Lemma 4.2 — fidelity $F(\rho_{p,\tau},\sigma)=\sqrt{pj\ell}\,T_j(\tau)+\sqrt{\lambda_f(1-pw(\tau))}$ and distinguishability of the mixture
-- statement:
--   Setting of §4.1: $\sigma=U\,\mathrm{diag}(\lambda)\,U^*$ is a state on $\mathbb C^d$; $J$ is a set of $j$ eigenvectors, $\ell=\min_{i\in J}\lambda_i>0$; $f\notin J$ is an eigenvector with $\lambda_f\le\ell$; $0<p\le1/2$; $\rho_{p,\tau}=(1-p)|f\rangle\langle f|+p\,\Phi(\tau)$ (Eq. (19)) and $w(\tau)=\mathrm{tr}(L\tau L^*)$.
--
--   1. For every state $\tau$ on $\mathbb C^j$,
--   $$F(\rho_{p,\tau},\sigma)=\sqrt{pj\ell}\;T_j(\tau)+\sqrt{\lambda_f\,(1-p\,w(\tau))}.$$
--   2. For every $\gamma>0$ and all states $\tau_0,\tau_1$ with $T_j(\tau_0)\le\gamma/4$ and $T_j(\tau_1)\ge\gamma$,
--   $$F(\rho_{p,\tau_1},\sigma)-F(\rho_{p,\tau_0},\sigma)\ \ge\ \Delta\sqrt{pj\ell}-p\sqrt{\lambda_f},\qquad\Delta=\tfrac{3\gamma}4 .$$
--   3. If $\Lambda_0,\Lambda_1$ are priors on states on $\mathbb C^j$ and $m\in\mathbb N$ with $d_{\mathrm{tr}}(\mathbb E_{\Lambda_0}\tau^{\otimes t},\mathbb E_{\Lambda_1}\tau^{\otimes t})\le 1/100$ for all $t\le m$, then whenever $np\le m/8$,
--   $$d_{\mathrm{tr}}\big(\mathbb E_{\Lambda_0}\rho_{p,\tau}^{\otimes n},\ \mathbb E_{\Lambda_1}\rho_{p,\tau}^{\otimes n}\big)\ \le\ \frac1{100}+\frac18<\frac13 .$$
--
--   Together with Lemma 2.1 and Proposition 4.1 this gives the lower bound (4) of Theorem 1.3.
--
--   Differences from the source:
--   - generalization: (21): if τ is sampled from the priors in Proposition 4.1, the two ranges of the fidelity are separated → for all states τ₀, τ₁ with T_j(τ₀) ≤ γ/4 and T_j(τ₁) ≥ γ (any γ > 0); reason: the pointwise statement implies the almost-sure one for the priors of Proposition 4.1
--   - reading: their n-copy average states (for the priors of Proposition 4.1) → for any priors Λ₀, Λ₁ on states and m with d_tr(E_{Λ₀}τ^{⊗t}, E_{Λ₁}τ^{⊗t}) ≤ 1/100 for all t ≤ m; reason: these are exactly the properties of Proposition 4.1's priors that the clause refers to
--   - encoding: J a set of j eigenvectors, ℂ^j identified with J, ℓ = λ_min(σ_J) → σ = U diag(λ) U* with U unitary, J : Fin j ↪ Fin d, the isometry of the columns U e_{J i}, ℓ the least λ_{J i} (IsLeast); reason: a choice of eigenbasis; covers degenerate spectra
--   - encoding: priors on states and the n-copy average states E_Λ ρ_{p,τ}^{⊗n}, E_Λ τ^{⊗t} → IsStatePrior (probability measure, a.s. a density matrix) and avgPower Λ (rhoMix …) n, avgPower Λ id t (entrywise integrals); reason: the same objects; the a.s. state condition keeps every integral genuine
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §4.1 (setting), p. 8 (PDF p. 10), and Lemma 4.2, p. 9 (PDF p. 11)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_rhoMix
import Definitions.Def_KnownFidelity_Rank_wJ
import Definitions.Def_KnownFidelity_Rank_fid
import Definitions.Def_KnownFidelity_Rank_Tj
import Definitions.Def_KnownFidelity_Rank_IsStatePrior
import Definitions.Def_KnownFidelity_Rank_avgPower
import Definitions.Def_KnownFidelity_Rank_traceDist

open MeasureTheory
open scoped Matrix

namespace KnownFidelity.Rank

/-- **Lemma 4.2 (Fidelity and distinguishability of the mixture).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §4.1 setting, printed p. 8 (PDF p. 10), and Lemma 4.2, printed p. 9 (PDF p. 11): "For every
state τ on J, F(ρ_{p,τ}, σ) = √(pjℓ) T_j(τ) + √(λ_f(1 − pw(τ))). (20) If τ is sampled from the
priors in proposition 4.1, the two ranges of this fidelity are separated by at least
∆√(pjℓ) − p√λ_f, ∆ = 3γ/4. (21) Their n-copy average states have trace distance at most
1/100 + 1/8 < 1/3 whenever np ≤ m/8."

Setting (§4.1): `σ = U diag(λ) U*` is a state on `ℂ^d` with `U` unitary; `J : Fin j ↪ Fin d`
selects `j` eigenvectors; `ℓ = min_i λ_{J i} > 0`; `f ∉ J` is an eigenvector with `λ_f ≤ ℓ`;
`0 < p ≤ 1/2`; `ρ_{p,τ} = rhoMix U λ J f ℓ p τ`. Three clauses:
(20) for every state `τ` on `ℂ^j`;
(21) for every `γ > 0` and all states `τ₀, τ₁` with `T_j(τ₀) ≤ γ/4` and `T_j(τ₁) ≥ γ`,
`F(ρ_{p,τ₁}, σ) − F(ρ_{p,τ₀}, σ) ≥ (3γ/4)√(pjℓ) − p√λ_f`;
(trace distance) for priors `Λ₀, Λ₁` on states on `ℂ^j` and `m` such that
`d_tr(E_{Λ₀} τ^{⊗t}, E_{Λ₁} τ^{⊗t}) ≤ 1/100` for all `t ≤ m` (the conclusion of
Proposition 4.1), every `n` with `np ≤ m/8` has
`d_tr(E_{Λ₀} ρ_{p,τ}^{⊗n}, E_{Λ₁} ρ_{p,τ}^{⊗n}) ≤ 1/100 + 1/8`, and `1/100 + 1/8 < 1/3`.

**Formalization Note.** "Identify C^j with J" is the isometry of the columns `U e_{J i}`
(`PhiMap`); `L = Lmat`, `w = wJ`, `F(ρ, σ) = fid ρ σ`, `T_j = Tj`. Clause (21) is stated
pointwise for any two states in the two ranges, which implies the almost-sure statement for the
priors of Proposition 4.1; the trace-distance clause takes exactly the conclusions of
Proposition 4.1 as hypotheses. The average `E_{Λ_b} ρ_{p,τ}^{⊗n}` is `avgPower Λ_b (rhoMix …) n`. -/
theorem lemma_4_2 {d j : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (lam : Fin d → ℝ) (σ : Matrix (Fin d) (Fin d) ℂ) (hσ : QAlgorithms.IsDensityMatrix σ)
    (hσU : σ = U * Matrix.diagonal (fun a => (lam a : ℂ)) * Uᴴ)
    (J : Fin j ↪ Fin d) (f : Fin d) (hf : f ∉ Set.range J) (ℓ : ℝ)
    (hℓ : IsLeast (Set.range fun i => lam (J i)) ℓ) (hℓpos : 0 < ℓ) (hfℓ : lam f ≤ ℓ)
    (p : ℝ) (hp : 0 < p) (hp2 : p ≤ 1 / 2) :
    (∀ τ : Matrix (Fin j) (Fin j) ℂ, QAlgorithms.IsDensityMatrix τ →
      fid (rhoMix U lam J f ℓ p τ) σ =
        Real.sqrt (p * j * ℓ) * Tj τ + Real.sqrt (lam f * (1 - p * wJ lam J ℓ τ))) ∧
    (∀ γ : ℝ, 0 < γ → ∀ τ₀ τ₁ : Matrix (Fin j) (Fin j) ℂ,
      QAlgorithms.IsDensityMatrix τ₀ → QAlgorithms.IsDensityMatrix τ₁ →
      Tj τ₀ ≤ γ / 4 → γ ≤ Tj τ₁ →
      3 * γ / 4 * Real.sqrt (p * j * ℓ) - p * Real.sqrt (lam f) ≤
        fid (rhoMix U lam J f ℓ p τ₁) σ - fid (rhoMix U lam J f ℓ p τ₀) σ) ∧
    (∀ (Λ₀ Λ₁ : Measure (Matrix (Fin j) (Fin j) ℂ)) (m : ℕ),
      IsStatePrior Λ₀ → IsStatePrior Λ₁ →
      (∀ t : ℕ, t ≤ m → traceDist (avgPower Λ₀ id t) (avgPower Λ₁ id t) ≤ 1 / 100) →
      ∀ n : ℕ, n * p ≤ m / 8 →
        traceDist (avgPower Λ₀ (rhoMix U lam J f ℓ p) n)
            (avgPower Λ₁ (rhoMix U lam J f ℓ p) n) ≤ 1 / 100 + 1 / 8 ∧
          (1 / 100 + 1 / 8 : ℝ) < 1 / 3) := by sorry

end KnownFidelity.Rank
