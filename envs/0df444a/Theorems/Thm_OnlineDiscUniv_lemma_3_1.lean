-- Prove2me | Theorems.Thm_OnlineDiscUniv_lemma_3_1
-- name    : OnlineDiscUniv.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:53.51633+00:00
-- url     : https://prove2.me/theorems/3c65e4a7-0b6e-44d7-9562-c54af82cc22b
-- title:
--   Lemma 3.1 — realizing a prescribed mean drift: $\mathbb E[\zeta_i\psi_\rho(\langle v,\zeta\rangle)]=\rho v_i+e_i$ and the bound on $t=\mathbb E\psi_\rho(\langle v,\zeta\rangle)$
-- statement:
--   Fix $0<\delta<c_*$ (3.3) and $L$ with $m_\delta=\mathbb E[G\tanh(LG)]>c_*-\delta/2$ (3.4), and let $\psi_\rho$ be as in (3.5). Let $\zeta_1,\dots,\zeta_M$ be independent copies of a law $\nu$ with mean $m$, variance $\sigma^2\in[1/2,2]$ and bounded third absolute moment; let $\|v\|_2=1$, $\|v\|_\infty\le1/2$ and $d=m\sum_jv_j$. For $0\le\rho\le c_*-\delta$,
--   $$
--   \mathbb E[\zeta_i\psi_\rho(\langle v,\zeta\rangle)]=\rho v_i+e_i,\qquad|e_i|\le C\rho\big[|v_i|(\|v\|_\infty+|\sigma^2-1|+|d|)+|m|\big],\qquad(3.8)
--   $$
--   and $t:=\mathbb E\psi_\rho(\langle v,\zeta\rangle)$ satisfies
--   $$
--   |t|\le C\rho\Big(\sum_j|v_j|^3+|d|\Big)\le C\rho(\|v\|_\infty+|d|).\qquad(3.9)
--   $$
--   The constant $C$ depends only on $\delta$ and the third-moment bound, not on $M$.
--
--   The lemma shows that the randomized sign rule (3.16) produces, in expectation, the prescribed drift direction $v$ with magnitude $\rho$, for non-Gaussian entries.
--
--   Differences from the source:
--   - generalization: L = L_δ < ∞ chosen so that (3.4) holds → every L with c_* − δ/2 < E[G tanh(LG)]; constants may depend on (δ, L, K₃); reason: the paper's L_δ is one such L, so the statement specializes to the source's
--   - reading: bounded third absolute moment; constants depend on the third-moment bound → E|ζ₁|³ ≤ K₃ (uncentered, lower integral), C chosen after (δ, L, K₃) and before M, ν, v, ρ, i; reason: with σ² ≤ 2 the centered and uncentered third moments bound each other up to constants, so neither reading is weaker; C uniform in M as the paper's constants are
--   - encoding: ‖v‖₂ = 1, ‖v‖_∞ ≤ 1/2, e_i defined by the display → ∑ v_j² = 1, sup norm ‖v‖ ≤ 1/2, e_i := E[ζ_iψ_ρ(⟨v,ζ⟩)] − ρv_i; the chain in (3.9) as two inequalities with the same C; reason: same quantities
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), Lemma 3.1, (3.3)–(3.9), p.7 (PDF p.8)

import Mathlib
import Definitions.Def_OnlineDiscUniv_psi

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv

/-- **Lemma 3.1** (Jo–Lee, arXiv:2610.00103, artifact sha256 cb190f12…, printed p.7, PDF p.8).
Fix `0 < δ < c_*` (3.3) and `L` with `m_δ = E[G tanh(LG)] > c_* − δ/2` (3.4). Let `ζ_1, …, ζ_M` be
independent copies of a law `ν` with mean `m`, variance `σ² ∈ [1/2, 2]`, and bounded third
absolute moment; let `‖v‖_2 = 1`, `‖v‖_∞ ≤ 1/2`, `d = m ∑_j v_j`. For `0 ≤ ρ ≤ c_* − δ`,
`E[ζ_i ψ_ρ(⟨v, ζ⟩)] = ρ v_i + e_i` with `|e_i| ≤ Cρ[|v_i|(‖v‖_∞ + |σ² − 1| + |d|) + |m|]` (3.8), and
`t := Eψ_ρ(⟨v, ζ⟩)` satisfies `|t| ≤ Cρ(∑_j |v_j|³ + |d|) ≤ Cρ(‖v‖_∞ + |d|)` (3.9). Constants depend
only on `δ` and the third-moment bound.

**Formalization Note** The constant `C` is chosen after `δ`, `L` and the bound `K₃` on
`E|ζ_1|³`, and before `M`, `ν`, `v`, `ρ`, `i`; it is uniform in the dimension `M`. The statement
holds for every `L` satisfying (3.4) (the paper fixes one such `L = L_δ`). `‖v‖_∞` is the sup norm
of `v : Fin M → ℝ`; `‖v‖_2 = 1` is `∑_j v_j² = 1`. "Third absolute moment" is `E|ζ_1|³`
(uncentered), a lower integral; it makes all the Bochner integrals below true expectations. -/
theorem lemma_3_1 (δ L K₃ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < cStar) (hL : cStar - δ / 2 < mL L) :
    ∃ C : ℝ, ∀ (M : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν],
      ∫⁻ x, ‖x‖ₑ ^ (3 : ℝ) ∂ν ≤ ENNReal.ofReal K₃ →
      1 / 2 ≤ ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν → ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν ≤ 2 →
      ∀ v : Fin M → ℝ, ∑ j, v j ^ 2 = 1 → ‖v‖ ≤ 1 / 2 →
      ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ cStar - δ → ∀ i : Fin M,
        let m : ℝ := ∫ y, y ∂ν
        let σ2 : ℝ := ∫ x, (x - m) ^ 2 ∂ν
        let d : ℝ := m * ∑ j, v j
        let e : ℝ := (∫ ζ, ζ i * psi L ρ (∑ j, v j * ζ j) ∂(Measure.pi fun _ : Fin M => ν)) -
          ρ * v i
        let t : ℝ := ∫ ζ, psi L ρ (∑ j, v j * ζ j) ∂(Measure.pi fun _ : Fin M => ν)
        |e| ≤ C * ρ * (|v i| * (‖v‖ + |σ2 - 1| + |d|) + |m|) ∧
        |t| ≤ C * ρ * (∑ j, |v j| ^ 3 + |d|) ∧
        |t| ≤ C * ρ * (‖v‖ + |d|) := by sorry

end OnlineDiscUniv
