-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_3
-- name    : MWCSherali.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:39.307916+00:00
-- url     : https://prove2.me/theorems/653df57f-fddd-4910-b762-799a5ad3e101
-- title:
--   Lemma 4.3 — corner flows
-- statement:
--   Assume $\tfrac12<\alpha<1$, $0<\beta<\tfrac{1-\alpha}2$ and $C>0$. For every $a\in[4]$ and every continuously differentiable $\varphi$,
--
--   $$I^{K_a}_a(\varphi)=\mu_a(\Delta_4)\,\varphi(e_a)-\int\varphi\,d\mu_a,$$
--
--   and $I^{K_a}_b(\varphi)=0$ for every $b\neq a$ (no other commodity flows in the corner $K_a$).
--
--   Here $I^{K_a}_c(\varphi)=\sum_{i\neq c}\int\nabla\varphi\cdot(e_c-e_i)\,dF^{K_a}_{c,i}$, with $F^{K_a}_{a,i}$ the corner flows along straight paths from $e_a$ to the exit measure $\mu_a$ and $F^{K_a}_{b,i}=0$ for $b\neq a$. The corner thus emits commodity $a$ at $e_a$ and delivers it to $\mu_a$.
--
--   Differences from the source:
--   - encoding: standing assumptions of §4: α, β > 0 with 1/2 < α < 1, 0 < β < (1 − α)/2, C > 0 (pp.31–32) → hypotheses 1/2 < α, α < 1, 0 < β, β < (1 − α)/2, 0 < C; reason: the section's standing assumptions, stated in the binders
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: indices a, b, i ∈ [4] (1-based) → Fin 4 (0-based); reason: Lean convention
--   - encoding: densities such as Cβ(w − 1 + α), Cβ/(t_i + t_j) → ENNReal.ofReal of the density; reason: the densities are nonnegative on their supports under the standing assumptions
--   - encoding: μ_a(Δ_4) → the real number (μ_a).real Δ_4; reason: μ_a is a finite measure
--   - encoding: commodity b's corner flows F^{K_a}_{b,i} (0 for b ≠ a) → the family i ↦ (if b = a then F^{K_a}_{a,i} else 0); reason: the paper sets all other measures in the corner to 0
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.3, p.33

import Mathlib
import Definitions.Def_MWCSherali_flowDiv
import Definitions.Def_MWCSherali_muCorner
import Definitions.Def_MWCSherali_FK

namespace MWCSherali

open MeasureTheory

/-- **Lemma 4.3 (corner flows).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.3, p.33: "For every `a ∈ [4]` and
`φ ∈ C^{(1)}(Δ₄)`, we have `I^{K_a}_a(φ) = μ_a(Δ₄)φ(e_a) − ∫ φ dμ_a`, and `I^{K_a}_b(φ) = 0` for any
`b ≠ a`."

In the corner `K_a` commodity `c`'s flow in direction `i` is `F^{K_a}_{a,i}` when `c = a` and `0`
otherwise ("all other measures are set to be 0 in this corner", p.33).

**Formalization Note.**
* Standing assumptions of §4 (p.31–32): `1/2 < α < 1`, `0 < β < (1 − α)/2`, `C > 0`.
* `φ ∈ C^{(1)}(Δ₄)` is read as `ContDiff ℝ 1 φ` on `ℝ⁴` (only values and tangential derivatives on
  `Δ₄` enter). `μ_a(Δ₄)` is the real number `(μ_a).real Δ₄`. Indices are 0-based. -/
theorem lemma_4_3 (α β C : ℝ) (hα : 1 / 2 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβα : β < (1 - α) / 2) (hC : 0 < C) (a : Fin 4) (φ : (Fin 4 → ℝ) → ℝ)
    (hφ : ContDiff ℝ 1 φ) :
    flowDiv 4 (fun i => FK α β C a i) a φ =
        (muCorner α β C a).real (stdSimplex ℝ (Fin 4)) * φ (Pi.single a 1) -
          ∫ t, φ t ∂(muCorner α β C a) ∧
      ∀ b, b ≠ a → flowDiv 4 (fun i => if b = a then FK α β C a i else 0) b φ = 0 := by sorry

end MWCSherali
