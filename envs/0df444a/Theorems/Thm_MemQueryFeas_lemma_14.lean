-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_14
-- name    : MemQueryFeas.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:36.028248+00:00
-- url     : https://prove2.me/theorems/728be925-b0d9-4b37-bec0-b683c29bd4d5
-- title:
--   Lemma 14 — small-ball bound $\Pr(\|P_WP_F\|_{op}\le\epsilon)\le(C_0\epsilon\rho\sqrt{d/\tilde d})^{k\tilde d}$
-- statement:
--   There is a universal constant $C_0>0$ such that the following holds. Fix $E_0\in\mathrm{Gr}(\tilde d,d)$, $\delta\in(0,1/d]$ and $\rho\ge1$. Sample $E\sim\mathrm{Unif}(B(E_0,\delta))$ and let $F=T_{E_0,\rho\delta}(E)$. Then for every fixed $W\in\mathrm{Gr}(k,d)$ and every $\epsilon>0$,
--   $$
--   \Pr\big(\|P_WP_F\|_{op}\le\epsilon\big)\le\Big(C_0\,\epsilon\,\rho\sqrt{\tfrac{d}{\tilde d}}\Big)^{k\tilde d}.
--   $$
--
--   After the stretch, a uniform subspace in a small Grassmannian ball behaves like a subspace with constant-order variability, so a fixed $k$-dimensional subspace is nearly orthogonal to it only with probability exponentially small in $k\tilde d$; this is the source of the $\tilde\Omega(k\tilde d)$ information requirement in Proposition 3.
--
--   Differences from the source:
--   - encoding: the printed statement for d̃ ≥ 1 (√(d/d̃) is undefined at d̃ = 0) → all d̃, with Lean's √(d/0) = 0 and exponent k·0 = 0, so the bound is 1 at d̃ = 0; reason: at d̃ = 0 the right side is 1 and the claim is trivially true; no instance of the source is changed
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 14, p.26 (PDF p.27); proof App. E, pp.38–40

import Mathlib
import Definitions.Def_MemQueryFeas_IsHaarGr
import Definitions.Def_MemQueryFeas_unifBall
import Definitions.Def_MemQueryFeas_imageProj
import Definitions.Def_MemQueryFeas_stretch

open MeasureTheory

namespace MemQueryFeas

/-- **Lemma 14 (small-ball probability for a stretched uniform subspace).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 14, p.26
(PDF p.27): "There is a universal constant `C_0 > 0` such that the following holds. Fix
`E_0 ∈ Gr(d̃, d)` and some parameters `δ ∈ (0, 1/d]` and `ρ ≥ 1`. Sample `E ∼ Unif(B(E_0, δ))` and let
`F := T_{E_0,ρδ}(E)`. Then, for any fixed subspace `W ∈ Gr(k, d)` and `ϵ > 0`, we have
`P(‖P_W P_F‖_op ≤ ϵ) ≤ (C_0 ϵ ρ √(d/d̃))^{k d̃}`."

**Formalization Note.** `C₀` is universal: chosen before `d, d̃, k` and everything else. `F` is the
image subspace `T_{E_0,ρδ}(E)` (`imageProj`); `P_W P_F` is the composition of projections and
`‖·‖` the operator norm. The law of `E` is `unifBall` of the Haar law `ν` of `Gr(d̃,d)`. -/
theorem lemma_14 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (d dt k : ℕ) (ν : Measure (Op d)), IsHaarGr dt ν →
      ∀ E₀ : Op d, IsOrthProj dt E₀ → ∀ δ ρ : ℝ, 0 < δ → δ ≤ 1 / d → 1 ≤ ρ →
      ∀ W : Op d, IsOrthProj k W → ∀ ϵ : ℝ, 0 < ϵ →
        unifBall ν dt E₀ δ {E | ‖W.comp (imageProj (stretch E₀ (ρ * δ)) E)‖ ≤ ϵ} ≤
          ENNReal.ofReal ((C₀ * ϵ * ρ * Real.sqrt (d / dt)) ^ (k * dt)) := by sorry

end MemQueryFeas
