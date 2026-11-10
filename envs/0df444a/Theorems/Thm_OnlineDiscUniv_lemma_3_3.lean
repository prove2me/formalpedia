-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_3_3
-- name    : OnlineDiscUniv.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:08.070313+00:00
-- url     : https://prove2.me/theorems/cb0e9b61-f14b-4869-9ce7-89b0e89a830c
-- title:
--   Lemma 3.3 — coupling $(\varepsilon,\zeta)$ to a fair sign $S$ and an independent $Z\sim\nu^{\otimes M}$
-- statement:
--   Under the hypotheses of Lemma 3.1, let $\varepsilon$ be chosen by (3.16). The pair $(\varepsilon,\zeta)$ can be coupled to a fair Rademacher sign $S$ and a vector $Z\sim\nu^{\otimes M}$ with $Z$ independent of $(\varepsilon,S)$ such that, writing $Y=\varepsilon\zeta$, for every $s\ge3$ with $\mathbb E|\zeta_1|^s<\infty$,
--   $$
--   \mathbb E|Y_i-SZ_i|^2\le C(\rho|v_i|+|t|),\qquad(3.20)
--   $$
--   $$
--   \mathbb E|Y_i-SZ_i|^s\le C_s\mathbb E|\zeta_1|^s,\qquad(3.21)
--   $$
--   and for $D=Y-SZ-\mathbb EY$ (3.22),
--   $$
--   \mathbb ED_i=0,\qquad\mathbb ED_i^2\le C\rho\big(|v_i|+\|v\|_\infty+\sqrt M|m|\big),\qquad\mathbb E|D_i|^s\le C_s\mathbb E|\zeta_1|^s.\qquad(3.23)
--   $$
--   The second-moment constants depend only on $\delta$ and a third-moment bound; the $s$-th moment enters linearly. For fixed $\nu$, the conditional law of $(S,Z)$ given $(\varepsilon,\zeta)$ is measurable in the parameters $(\rho,v,t)$ and the observed pair.
--
--   This is the exact decomposition $\varepsilon\zeta=SZ+r/\sqrt N+e+D$ that lets the signed non-Gaussian increments be compared with independent ones.
--
--   Differences from the source:
--   - generalization: L = L_δ < ∞ chosen so that (3.4) holds → every L with c_* − δ/2 < E[G tanh(LG)]; constants may depend on (δ, L, K₃); reason: the paper's L_δ is one such L, so the statement specializes to the source's
--   - encoding: the conditional law of (S, Z) given (ε, ζ) is measurable in (ρ, v, t) and the observed pair → a Markov kernel κ from ((ρ, v), (ε, ζ)) to (S, Z), chosen after ν; the coupling is steerLaw ⊗ₘ κ(ρ, v, ·); reason: t is a measurable function of (ρ, v) for fixed ν, so measurability in (ρ, v, t) and in (ρ, v) are the same; one coupling satisfies all bounds
--   - reading: C_s (the s-th moment enters linearly) → a function s ↦ C_s chosen after (δ, L, K₃) and before M, ν; reason: the paper does not list what C_s depends on besides s; it is uniform in M and ν as displayed
--   - encoding: ED_i = 0 and the absolute moments → D_i integrable and ∫ D_i = 0; absolute moments as lower integrals; reason: D_i is integrable under the third-moment bound, so the statements coincide
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma 3.3, (3.20)–(3.23), p.8 (PDF p.9)

import Mathlib
import Definitions.Def_OnlineDiscUniv_steerLaw
import Definitions.Def_OnlineDiscUniv_radVec

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Lemma 3.3** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.8, PDF p.9).
Under the hypotheses of Lemma 3.1, let `ε` be chosen by (3.16). Couple the pair `(ε, ζ)` to a fair
Rademacher sign `S` and a vector `Z ∼ ν^{⊗M}` with `Z` independent of `(ε, S)`. Writing `Y = εζ`,
one can arrange, for every `s ≥ 3` with `E|ζ_1|^s < ∞`, `E|Y_i − SZ_i|² ≤ C(ρ|v_i| + |t|)` (3.20),
`E|Y_i − SZ_i|^s ≤ C_s E|ζ_1|^s` (3.21), and for `D = Y − SZ − EY` (3.22): `ED_i = 0`,
`ED_i² ≤ Cρ(|v_i| + ‖v‖_∞ + √M|m|)`, `E|D_i|^s ≤ C_s E|ζ_1|^s` (3.23). The second-moment constants
depend only on `δ` and a third-moment bound. For fixed `ν`, the conditional law of `(S, Z)` given
`(ε, ζ)` is measurable in the parameters and the observed pair.

**Formalization Note** One coupling satisfies all bounds at once. It is given by a Markov kernel
`κ` (measurable by construction) from (parameters `(ρ, v)`, observed pair `(ε, ζ)`) to `(S, Z)`,
chosen after `ν`; the joint law is `steerLaw ν L ρ v ⊗ₘ κ(ρ, v, ·)`, whose first marginal is the
law of `(ε, ζ)`. The parameter `t` is the function `Eψ_ρ(⟨v,ζ⟩)` of `(ρ, v, ν)`, so `(ρ, v)`
suffices. `C` and the function `s ↦ C_s` are chosen after `δ, L, K₃` and before `M`, `ν`.
Absolute moments are lower integrals; `ED_i = 0` is stated together with integrability of `D_i`. -/
theorem lemma_3_3 (δ L K₃ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < cStar) (hL : cStar - δ / 2 < mL L) :
    ∃ (C : ℝ) (Cs : ℝ → ℝ), ∀ (M : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫⁻ x, ‖x‖ₑ ^ (3 : ℝ) ∂ν ≤ ENNReal.ofReal K₃ →
      1 / 2 ≤ ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν → ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν ≤ 2 →
      ∃ κ : Kernel ((ℝ × (Fin M → ℝ)) × (ℝ × (Fin M → ℝ))) (ℝ × (Fin M → ℝ)),
        IsMarkovKernel κ ∧
        ∀ (ρ : ℝ) (v : Fin M → ℝ), 0 ≤ ρ → ρ ≤ cStar - δ → ∑ j, v j ^ 2 = 1 → ‖v‖ ≤ 1 / 2 →
          let m : ℝ := ∫ y, y ∂ν
          let t : ℝ := ∫ x, psi L ρ (∑ j, v j * x j) ∂(Measure.pi fun _ : Fin M => ν)
          let Γ : Measure ((ℝ × (Fin M → ℝ)) × (ℝ × (Fin M → ℝ))) :=
            steerLaw ν L ρ v ⊗ₘ κ.sectR (ρ, v)
          let Y : Fin M → (ℝ × (Fin M → ℝ)) × (ℝ × (Fin M → ℝ)) → ℝ := fun i q => q.1.1 * q.1.2 i
          let SZ : Fin M → (ℝ × (Fin M → ℝ)) × (ℝ × (Fin M → ℝ)) → ℝ :=
            fun i q => q.2.1 * q.2.2 i
          let D : Fin M → (ℝ × (Fin M → ℝ)) × (ℝ × (Fin M → ℝ)) → ℝ :=
            fun i q => Y i q - SZ i q - ∫ q', Y i q' ∂Γ
          Γ.map (fun q => q.2.1) = fairCoin ∧
          Γ.map (fun q => q.2.2) = Measure.pi (fun _ : Fin M => ν) ∧
          IndepFun (fun q => q.2.2) (fun q => (q.1.1, q.2.1)) Γ ∧
          (∀ i, ∫⁻ q, ‖Y i q - SZ i q‖ₑ ^ (2 : ℝ) ∂Γ ≤ ENNReal.ofReal (C * (ρ * |v i| + |t|))) ∧
          (∀ i, Integrable (D i) Γ ∧ ∫ q, D i q ∂Γ = 0 ∧
            ∫⁻ q, ‖D i q‖ₑ ^ (2 : ℝ) ∂Γ ≤
              ENNReal.ofReal (C * ρ * (|v i| + ‖v‖ + Real.sqrt M * |m|))) ∧
          ∀ s : ℝ, 3 ≤ s → ∫⁻ x, ‖x‖ₑ ^ s ∂ν < ⊤ → ∀ i,
            ∫⁻ q, ‖Y i q - SZ i q‖ₑ ^ s ∂Γ ≤ ENNReal.ofReal (Cs s) * ∫⁻ x, ‖x‖ₑ ^ s ∂ν ∧
            ∫⁻ q, ‖D i q‖ₑ ^ s ∂Γ ≤ ENNReal.ofReal (Cs s) * ∫⁻ x, ‖x‖ₑ ^ s ∂ν := by sorry

end OnlineDiscUniv
