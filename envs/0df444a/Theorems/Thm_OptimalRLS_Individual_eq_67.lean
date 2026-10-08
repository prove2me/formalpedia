-- Prove2me | Theorems.Thm_OptimalRLS_Individual_eq_67
-- name    : OptimalRLS.Individual.eq_67
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:19:40.096545+00:00
-- url     : https://prove2.me/theorems/21b22dd8-b70f-422a-80cc-cabbbcd5c675
-- title:
--   (67), pp. 28–30 — averaged over random signs S, E R_ℓ(S) ≥ Φ(−1/σ) Σ_{n∈D_ℓ} γₙ
-- statement:
--   The setting is that of the proof of Theorem 3: Hypothesis 1 and $\dim Y = d < \infty$; a probability measure $\nu$ on $X$ with an eigen-system $(t_n, e_n)$ of $T$ satisfying (17); $B > b$; $\gamma_n$, $m^{(s)}$, $\sigma^2$ and $\rho_s$ as there.
--
--   Fix $\ell$ and a measurable estimator $\mathbf z \mapsto f_{\mathbf z}^\ell$ from samples $\mathbf z \in Z^\ell$ to $\mathcal H$. Let $\tilde c_{\mathbf z, n}$ be the sign of $c_{\mathbf z, n} = \sqrt{t_n/\gamma_n}\,\langle f^\ell_{\mathbf z}, e_n\rangle$, and let $\mathcal D_\ell = \{n : \ell\gamma_n \le 1\}$. For a sign sequence $s$, define as in (65)
--   $$R_\ell(s) = \sum_{n \in \mathcal D_\ell} P_{\mathbf z \sim \rho_s^\ell}\big[\tilde c_{\mathbf z, n} \ne s_n\big]\, \gamma_n .$$
--   Let $S = (S_i)$ be independent random signs with $P[S_i = +1] = P[S_i = -1] = 1/2$. Then
--   $$\mathbb E\, R_\ell(S) \ \ge\ \Phi\Big(-\frac1\sigma\Big) \sum_{n \in \mathcal D_\ell} \gamma_n ,$$
--   where $\Phi$ is the standard normal distribution function. This is (67) with the constant $C = \Phi(-1/\sigma) > 0$ that the proof obtains.
--
--   Averaging over random signs is what turns a worst-case lower bound into an individual one: combined with (68) and Fatou's lemma it yields a single sign sequence, hence a single distribution, that is hard for all large $\ell$.
--
--   **Formalization Note** $S$ is encoded as independent fair coins $\omega \in \mathrm{Bool}^{\mathbb N}$ mapped to signs. $\mathbb E\,R_\ell(S)$ is a `lintegral` with values in $[0, \infty]$ of the function $\omega \mapsto R_\ell(\mathrm{sgn}\circ\omega)$, and probabilities of events are measures of sets. The sums over $\mathcal D_\ell$ are `tsum`s with an indicator of $\ell\gamma_n \le 1$. Indices start at $0$.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proof of Th. 3, (65) p. 27, (67) p. 28, and the proof of (67) concluding "with C = Φ(−1/σ)" on p. 30

import Mathlib
import Definitions.Def_OptimalRLS_Individual_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

namespace OptimalRLS.Individual

variable {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [TopologicalSpace.SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [MeasurableSpace H] [BorelSpace H] [RKHS ℝ H X Y]

/-- **(67)** (pp. 28–30), with the constant the proof obtains, `C = Φ(−1/σ)`. Fix `ℓ` and a
measurable estimator `f_ℓ : Z^ℓ → H`. For a sign sequence `s`, (65) defines
`R_ℓ(s) = ∑_{n ∈ D_ℓ} P_{z∼ρ_s^ℓ}[c̃_{z,n} ≠ s_n] γ_n`, `D_ℓ = {n | ℓ γ_n ≤ 1}`, where `ρ_s` has
marginal `ν` and conditional `N(m^{(s)}(x), σ² Id)` and `c̃_{z,n}` is the sign of
`c_{z,n} = √(t_n/γ_n)⟨f_z^ℓ, e_n⟩`. For `S` a sequence of independent fair signs,
`E R_ℓ(S) ≥ Φ(−1/σ) ∑_{n ∈ D_ℓ} γ_n`.
`S` is encoded as independent fair coins `ω : ℕ → Bool` (`signLaw`) read through `sgn`. -/
theorem eq_67 {ι : Type*} (κ : ℝ) (v : HilbertBasis ι ℝ Y) (h1 : Hyp1 X H κ v)
    (M Sig R α β : ℝ) (hM : 0 < M) (hSig : 0 < Sig) (hR : 0 < R) (hα : 0 < α) (hβ : 0 < β)
    (b c : ℝ) (hb : 1 < b) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (B : ℝ) (hB : b < B)
    (ν : Measure X) [IsProbabilityMeasure ν] (e : ℕ → H) (t : ℕ → ℝ)
    (heig : IsEigenSystem ν e t) (hanti : Antitone t)
    (h17 : ∀ n : ℕ, α ≤ ((n : ℝ) + 1) ^ b * t n ∧ ((n : ℝ) + 1) ^ b * t n ≤ β)
    (ℓ : ℕ) (est : (Fin ℓ → X × Y) → H) (hest : Measurable est) :
    let γ := gam b c ((B - b) * c) α R
    let σ2 := sig2 M Sig (Module.finrank ℝ Y)
    let Rℓ : (ℕ → ℝ) → ℝ≥0∞ := fun s =>
      ∑' n, if (ℓ : ℝ) * γ n ≤ 1 then
          (Measure.pi fun _ : Fin ℓ => rhoS ν (mS e t γ s) σ2)
              {z | ctil e t γ (est z) n ≠ s n} * ENNReal.ofReal (γ n)
        else 0
    ENNReal.ofReal (Phi (-(1 / Real.sqrt σ2)) * ∑' n, (if (ℓ : ℝ) * γ n ≤ 1 then γ n else 0))
      ≤ ∫⁻ ω, Rℓ (fun n => sgn (ω n)) ∂signLaw := by sorry

end OptimalRLS.Individual
