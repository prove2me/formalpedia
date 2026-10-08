-- Prove2me | Theorems.Thm_IsingLTL_FreeEntropy_lemma_4_6_mk_lipschitz
-- name    : IsingLTL.FreeEntropy.lemma_4_6_mk_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:12:11.608981+00:00
-- url     : https://prove2.me/theorems/af618320-b5b3-4a99-b68f-33fbfeb01829
-- title:
--   Lemma 4.6 — $\|\tanh(h^*_{\beta_2})-\tanh(h^*_{\beta_1})\|_{\mathrm{MK}}\le C|\beta_2-\beta_1|$
-- statement:
--   Let $P$ be a degree distribution whose size-biased law $\rho$ has finite first moment. For any $B>0$ and finite $\beta_{\max}$ there is a constant $C$ such that, if $h^*_{\beta_1}$ and $h^*_{\beta_2}$ are the fixed points of the recursion (2.6) supported on $[0,\infty)$ at inverse temperatures $0\le\beta_1,\beta_2\le\beta_{\max}$ (and field $B$), then
--   $$\|\tanh(h^*_{\beta_2})-\tanh(h^*_{\beta_1})\|_{\mathrm{MK}}\le C\,|\beta_2-\beta_1|.$$
--
--   The law of the cavity field depends Lipschitz-continuously on $\beta$ in the Monge–Kantorovich distance.
--
--   **Formalization Note** The paper writes $C=C(\beta_{\max},B)$ and leaves the dependence on $\rho$ implicit; its proof uses a constant depending on $\bar\rho$, so $C$ is chosen after $P$, $B$ and $\beta_{\max}$, and before $\beta_1,\beta_2$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 18, Lemma 4.6, (4.16)

import Mathlib
import Definitions.Def_IsingLTL_FreeEntropy_DistRecursion
import Definitions.Def_IsingLTL_FreeEntropy_MKDist

namespace IsingLTL.FreeEntropy

open MeasureTheory

/-- **Lemma 4.6** (Dembo–Montanari, arXiv:0804.4726v3, p. 18, eq. (4.16)). Let `‖X − Y‖_MK` denote
the Monge–Kantorovich–Wasserstein distance between the laws of `X` and `Y` (the infimum of
`E|X − Y|` over all couplings). For any `B > 0` and `β_max` finite there exists a constant
`C = C(β_max, B)` such that if `h*_{β₁}`, `h*_{β₂}` are the fixed points of the recursion (2.6) for
`0 ≤ β₁, β₂ ≤ β_max`, then `‖tanh(h*_{β₂}) − tanh(h*_{β₁})‖_MK ≤ C |β₂ − β₁|`.

Formalization Note: `h*_β` is the fixed point of Lemma 2.3, i.e. a fixed point of (2.6) at
`(β, B)` supported on `[0, ∞)` (unique by Lemma 2.3); the statement is made for every such pair of
fixed points. The recursion depends on the degree distribution, and so does the constant (the
proof's `M = M(β_max, B, ρ̄)`): `C` is chosen after `P` (with `ρ` of finite first moment), `B` and
`β_max`, and before `β₁, β₂`. `tanh(h)` is the push-forward law of `h` under `tanh`. -/
theorem lemma_4_6_mk_lipschitz (D : DegreeDist) (hρ : D.RhoFiniteMean) (B βmax : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, ∀ (β₁ β₂ : ℝ) (Q₁ Q₂ : ProbabilityMeasure ℝ),
      0 ≤ β₁ → β₁ ≤ βmax → 0 ≤ β₂ → β₂ ≤ βmax →
      IsNonnegFixedPoint β₁ B D Q₁ → IsNonnegFixedPoint β₂ B D Q₂ →
      mkDist ((Q₂ : Measure ℝ).map Real.tanh) ((Q₁ : Measure ℝ).map Real.tanh) ≤
        ENNReal.ofReal (C * |β₂ - β₁|) := by sorry

end IsingLTL.FreeEntropy
