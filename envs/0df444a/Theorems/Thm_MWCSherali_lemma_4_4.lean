-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_4
-- name    : MWCSherali.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:31.013748+00:00
-- url     : https://prove2.me/theorems/ab8becc4-b69a-4346-bbe1-f9741fe94159
-- title:
--   Lemma 4.4 — simplex-edge flows
-- statement:
--   Assume $\tfrac12<\alpha<1$, $0<\beta<\tfrac{1-\alpha}2$ and $C>0$. For distinct $a,b\in[4]$ and every continuously differentiable $\varphi$,
--
--   $$I^{E_{ab}}_a(\varphi)=\int\varphi\,d\mu^E_{ab}-C\beta\int_{1-\alpha}^{\alpha}\varphi\big(y_{ab}(w)\big)\,dw,$$
--
--   where $\mu^E_{ab}=C\beta(2\alpha-1)\delta_{y_{ab}(\alpha)}$ is the atom (11). Furthermore $I^{E_{ab}}_i(\varphi)=0$ for every $i\in[4]\setminus\{a,b\}$.
--
--   On the edge $E_{ab}$ only commodity $a$ flows, in direction $b$: it receives the atom from the corner and sheds into the tube at the constant rate $C\beta$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: α, β > 0 with 1/2 < α < 1, 0 < β < (1 − α)/2, C > 0 (pp.31–32) → hypotheses 1/2 < α, α < 1, 0 < β, β < (1 − α)/2, 0 < C; reason: the section's standing assumptions, stated in the binders
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: indices a, b, i ∈ [4] (1-based) → Fin 4 (0-based); reason: Lean convention
--   - encoding: densities such as Cβ(w − 1 + α), Cβ/(t_i + t_j) → ENNReal.ofReal of the density; reason: the densities are nonnegative on their supports under the standing assumptions
--   - encoding: commodity c's edge flows F^{E_{ab}}_{c,l} → the family l ↦ (if c = a ∧ l = b then F^{E_{ab}}_{a,b} else 0); reason: commodity a's only flow on E_{ab} is F^{E_{ab}}_{a,b} (p.34); the edge's commodity-b flow F^{E_{ab}}_{b,a} (counted on p.41) belongs to commodity b, so it enters neither I^{E_{ab}}_a nor I^{E_{ab}}_i for i ∉ {a, b}
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.4, p.34

import Mathlib
import Definitions.Def_MWCSherali_flowDiv
import Definitions.Def_MWCSherali_yab
import Definitions.Def_MWCSherali_muE
import Definitions.Def_MWCSherali_FE

namespace MWCSherali

open MeasureTheory

/-- **Lemma 4.4 (simplex-edge flows).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.4, p.34: "For every distinct
`a, b ∈ [4]` and `φ ∈ C^{(1)}(Δ₄)`, we have
`I^{E_{ab}}_a(φ) = ∫ φ dμ^E_{ab} − Cβ ∫_{1−α}^{α} φ(y_{ab}(w)) dw`, where `μ^E_{ab}` is defined as in
Equation (11). Furthermore, `I^{E_{ab}}_i(φ) = 0` for any `i ∈ [4] ∖ {a, b}`."

On the edge `E_{ab}` commodity `c`'s flow in direction `l` is `F^{E_{ab}}_{a,b}` when `c = a` and
`l = b`, and `0` otherwise.

**Formalization Note.**
* Standing assumptions of §4 (p.31–32): `1/2 < α < 1`, `0 < β < (1 − α)/2`, `C > 0`.
* `φ ∈ C^{(1)}(Δ₄)` is read as `ContDiff ℝ 1 φ` on `ℝ⁴`. The `dw` integral is the interval
  integral over `[1 − α, α]`. Indices are 0-based. -/
theorem lemma_4_4 (α β C : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβα : β < (1 - α) / 2) (hC : 0 < C) (a b : Fin 4) (hab : a ≠ b) (φ : (Fin 4 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    flowDiv 4 (fun l => if l = b then FE α β C a b else 0) a φ =
        ∫ t, φ t ∂(muE α β C a b) - C * β * ∫ w in (1 - α)..α, φ (yab a b w) ∧
      ∀ i, i ≠ a → i ≠ b →
        flowDiv 4 (fun l => if i = a ∧ l = b then FE α β C a b else 0) i φ = 0 := by sorry

end MWCSherali
