-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_5
-- name    : MWCSherali.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:14:35.572186+00:00
-- url     : https://prove2.me/theorems/73f9c578-ca64-4e42-a120-7ba85e3438a9
-- title:
--   Lemma 4.5 — tube flows
-- statement:
--   Assume $\tfrac12<\alpha<1$, $0<\beta<\tfrac{1-\alpha}2$ and $C>0$. For distinct $a,b\in[4]$ and every continuously differentiable $\varphi$,
--
--   $$I^{T_{ab}}_a(\varphi)=\int\varphi\,d\mu^T_{ab}+C\beta\int_{1-\alpha}^{\alpha}\varphi\big(y_{ab}(w)\big)\,dw-\int\varphi\,d\eta_{ab},$$
--
--   where $\mu^T_{ab}$ is the measure (10) and $\eta_{ab}$ the measure (13). Furthermore $I^{T_{ab}}_i(\varphi)=0$ for every $i\in[4]\setminus\{a,b\}$.
--
--   In the tube $T_{ab}$ commodity $a$ receives flow from its corner and from the simplex edge, and passes it on to the central region.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: α, β > 0 with 1/2 < α < 1, 0 < β < (1 − α)/2, C > 0 (pp.31–32) → hypotheses 1/2 < α, α < 1, 0 < β, β < (1 − α)/2, 0 < C; reason: the section's standing assumptions, stated in the binders
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: indices a, b, i ∈ [4] (1-based) → Fin 4 (0-based); reason: Lean convention
--   - encoding: densities such as Cβ(w − 1 + α), Cβ/(t_i + t_j) → ENNReal.ofReal of the density; reason: the densities are nonnegative on their supports under the standing assumptions
--   - encoding: commodity c's tube flows F^{T_{ab}}_{c,l} → the family l ↦ (if (c = a ∨ c = b) ∧ l ∉ {a, b} then F^{T_{ab}}_{a,l} else 0); reason: commodities a and b share the tube flows in directions i, j; all other measures are 0 (p.35)
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.5, p.35

import Mathlib
import Definitions.Def_MWCSherali_flowDiv
import Definitions.Def_MWCSherali_yab
import Definitions.Def_MWCSherali_muT
import Definitions.Def_MWCSherali_FT
import Definitions.Def_MWCSherali_eta

namespace MWCSherali

open MeasureTheory

/-- **Lemma 4.5 (tube flows).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.5, p.35: "For every distinct `a, b ∈ [4]`
and `φ ∈ C^{(1)}(Δ₄)`, we have
`I^{T_{ab}}_a(φ) = ∫ φ dμ^T_{ab} + Cβ ∫_{1−α}^{α} φ(y_{ab}(w)) dw − ∫ φ dη_{ab}`, where `μ^T_{ab}` is
defined as in Equation (10). Furthermore, `I^{T_{ab}}_i(φ) = 0` for any `i ∈ [4] ∖ {a, b}`."

In the tube `T_{ab}` commodity `c`'s flow in direction `l` is `F^{T_{ab}}_{c,l}` (`FT a b l`) when
`c ∈ {a, b}` and `l ∉ {a, b}`, and `0` otherwise ("All other measures are set to 0", p.35).

**Formalization Note.**
* Standing assumptions of §4 (p.31–32): `1/2 < α < 1`, `0 < β < (1 − α)/2`, `C > 0`.
* `φ ∈ C^{(1)}(Δ₄)` is read as `ContDiff ℝ 1 φ` on `ℝ⁴`. The `dw` integral is the interval
  integral over `[1 − α, α]`. Indices are 0-based. -/
theorem lemma_4_5 (α β C : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβα : β < (1 - α) / 2) (hC : 0 < C) (a b : Fin 4) (hab : a ≠ b) (φ : (Fin 4 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    flowDiv 4 (fun l => if l ≠ a ∧ l ≠ b then FT α β C a b l else 0) a φ =
        ∫ t, φ t ∂(muT α β C a b) + C * β * ∫ w in (1 - α)..α, φ (yab a b w) -
          ∫ t, φ t ∂(eta α β C a b) ∧
      ∀ i, i ≠ a → i ≠ b →
        flowDiv 4 (fun l => if (i = a ∨ i = b) ∧ l ≠ a ∧ l ≠ b then FT α β C a b l else 0)
          i φ = 0 := by sorry

end MWCSherali
