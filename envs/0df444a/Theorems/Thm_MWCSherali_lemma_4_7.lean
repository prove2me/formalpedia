-- Prove2me | Theorems.Thm_MWCSherali_lemma_4_7
-- name    : MWCSherali.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:15:47.172199+00:00
-- url     : https://prove2.me/theorems/8d3e07f2-c3ec-4bf3-93bc-6ee2382a46c6
-- title:
--   Lemma 4.7 — central region
-- statement:
--   Assume $\beta>0$, $\tfrac12<\alpha\le1-3\beta$, (17), and $C>0$, and use the density vectors of Lemma 4.6. For every $a\in[4]$ and every continuously differentiable $\varphi$,
--
--   $$I^Z_a(\varphi)=\int\varphi\,d\mu^Z_a+\sum_{b\neq a}\int\varphi\,d\eta_{ab}-\int\varphi\,d\nu_a,$$
--
--   where $\mu^Z_a$ is the measure (9), $\eta_{ab}$ the measure (13), and $d\nu_a=C\,dt_i\,dt_j$ on $Z\cap\Gamma_a$ ($i\neq j\in[4]\setminus\{a\}$).
--
--   Commodity $a$ enters the central region from its corner and from its three tubes, and leaves through the sink face $Z\cap\Gamma_a$.
--
--   Differences from the source:
--   - encoding: φ ∈ C^{(1)}(Δ_k), continuously differentiable on Δ_k → ContDiff ℝ 1 φ on all of ℝ^k; reason: the constraints use only values on Δ_k and derivatives tangent to Δ_k, and every C¹ function on Δ_k agrees there with a global C¹ function
--   - encoding: indices a, b, i ∈ [4] (1-based) → Fin 4 (0-based); reason: Lean convention
--   - encoding: densities such as Cβ(w − 1 + α), Cβ/(t_i + t_j) → ENNReal.ofReal of the density; reason: the densities are nonnegative on their supports under the standing assumptions
--   - reading: Lemma 4.7 (stated without hypotheses, within §4.4) → hypotheses of Lemma 4.6 on α, β (β > 0, 1/2 < α ≤ 1 − 3β, (17)) and C > 0; reason: the lemma uses Lemma 4.6's density vectors, which are defined and valid under these assumptions; C > 0 is the standing assumption of p.32
--   - encoding: F^Z_{a,i} = B^Z_i for i ≠ a, the sum over the 72 tetrahedra → BZ i: the sum over (representative r, permutation π) of C c^{T_r}_{π⁻¹ i} dt on π·T_r, with factor 1/2; reason: each tetrahedron occurs exactly twice in the (r, π) sum, with the same density vector
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.7, p.40

import Mathlib
import Definitions.Def_MWCSherali_flowDiv
import Definitions.Def_MWCSherali_muZ
import Definitions.Def_MWCSherali_eta
import Definitions.Def_MWCSherali_nuZ
import Definitions.Def_MWCSherali_BZ

namespace MWCSherali

open MeasureTheory

/-- **Lemma 4.7 (central region).** Brakensiek–Huang–Potechin–Zwick, arXiv:2611.05511 (version of Nov. 3, 2026), Lemma 4.7, p.40: "For every `a ∈ [4]` and
`φ ∈ C^{(1)}(Δ₄)`, we have `I^Z_a(φ) = ∫ φ dμ^Z_a + ∑_{b ≠ a} ∫ φ dη_{ab} − ∫ φ dν_a`, where `dμ^Z_a` is
defined as in (9), `dη_{ab}` is defined as in (13), and `dν_a` is defined on `Z ∩ Γ_a` via
`dν_a = C dt_i dt_j`, `i ≠ j ∈ [4] ∖ {a}`."

Commodity `a`'s central flow in direction `i ≠ a` is `F^Z_{a,i} = B^Z_i` (p.38, p.40), built from
Lemma 4.6's density vectors.

**Formalization Note.**
* Hypotheses: Lemma 4.6's assumptions on `α, β` (`β > 0`, `1/2 < α ≤ 1 − 3β`, (17)), under which
  its density vectors are the ones used, and `C > 0` (p.32). They imply the standing
  assumptions `α < 1`, `β < (1 − α)/2` of p.31.
* `φ ∈ C^{(1)}(Δ₄)` is read as `ContDiff ℝ 1 φ` on `ℝ⁴`. Indices are 0-based. -/
theorem lemma_4_7 (α β C : ℝ) (hβ : 0 < β) (hα : 1 / 2 < α) (hαβ : α ≤ 1 - 3 * β)
    (h17 : 4 * (1 - α) ^ 2 - 24 * (1 - α) * β + 6 * β ^ 2 + 12 * β - 1 = 0) (hC : 0 < C)
    (a : Fin 4) (φ : (Fin 4 → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    flowDiv 4 (fun i => BZ α β C i) a φ =
      ∫ t, φ t ∂(muZ α β C a) + ∑ b ∈ Finset.univ.filter (· ≠ a), ∫ t, φ t ∂(eta α β C a b) -
        ∫ t, φ t ∂(nuZ α β C a) := by sorry

end MWCSherali
