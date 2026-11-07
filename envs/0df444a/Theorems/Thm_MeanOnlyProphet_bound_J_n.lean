-- Prove2me | Theorems.Thm_MeanOnlyProphet_bound_J_n
-- name    : MeanOnlyProphet.bound_J_n
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:35.963803+00:00
-- url     : https://prove2.me/theorems/2ae2d056-7541-49a5-9131-0f8de5fc24ba
-- title:
--   §A.2 — finite-$n$ bound $\mathbb E[\mathrm{ALG}]\ge J_n(b,r)$
-- statement:
--   Let $b$ be a drop rate whose threshold $\theta(t)=\int_t^1b$ is strictly decreasing on $[0,1]$ with $\theta(0)\le1$. Let $n\ge1$ and let $X_1,\dots,X_n$ be i.i.d. nonnegative with law $\mu$, normalized so that $\mathbb E[X^*]=1$, and let $r(t)=-n\log F(\theta(t))$. Then the randomly shifted rule with threshold $\theta$ satisfies
--   $$
--   \mathbb E[\mathrm{ALG}]\ \ge\ J_n(b,r)=C(r)\,A_P(0)+\int_0^1 b(t)\,T_n(t)\,dt,\qquad C(r)=1-\theta(0)+\int_0^1b(t)\,e^{-r(t)}\,dt .
--   $$
--   It is the finite-$n$ counterpart of the bound $\mathbb E[\mathrm{ALG}]\ge L$, obtained from the reward decomposition (A.1), a union bound and Lemma A.3.
--
--   Differences from the source:
--   - generalization: the drop rate b of the threshold being analysed (Theorem 3.5's forty-slope b) → every b whose threshold θ = ∫_t^1 b is strictly decreasing on [0,1] with θ(0) ≤ 1; reason: the derivation on pp.28–29 uses only these properties of θ and b; it specializes to the forty-slope b
--   - encoding: b(t) = −θ′(t) ≥ 0 almost everywhere, b integrable → not stated as hypotheses; reason: both follow from the strict decrease of θ = thetaOf b on [0,1] with θ(1) = 0 (a non-integrable b gives θ(0) = 0 = θ(1) in Lean)
--   - encoding: E[X*] = 1 → prophetMean μ n = 1; reason: this also makes the maximum, hence μ, integrable
--   - encoding: r(t) = −n · log F(θ(t)), log 0 = −∞ → rateOf μ n θ : ℝ → ℝ≥0∞; reason: e^{−∞} = 0
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.2, pp.28–29 (PDF pp.29–30)

import Mathlib
import Definitions.Def_MeanOnlyProphet_expectedReward
import Definitions.Def_MeanOnlyProphet_rateOf
import Definitions.Def_MeanOnlyProphet_Jn

open MeasureTheory

namespace MeanOnlyProphet

/-- **§A.2, the finite-`n` lower bound `E[ALG] ≥ J_n(b, r)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2, p.29 (PDF p.30): "Define
C(r) = 1 − θ(0) + ∫_0^1 b(t) · e^{−r(t)} dt. Now we can lower-bound the expected reward for finite n by
E[ALG] ≥ Jn (b, r) := C(r) · AP (0) + ∫_0^1 b(t) · Tn (t) dt."

For a drop rate `b` whose threshold `θ(t) = ∫_t^1 b` is strictly decreasing on `[0,1]` with `θ(0) ≤ 1`,
`n ≥ 1` i.i.d. nonnegative values with law `μ` normalized by `E[X*] = 1`, and `r(t) = −n · log F(θ(t))`,
the randomly shifted rule earns at least `J_n(b, r)`.

**Formalization Note.** `E[X*] = 1` is `prophetMean μ n = 1`; it also makes `X*` (hence `μ`)
integrable. `b ≥ 0` a.e. on `[0,1]` and the integrability of `b` are implied by the strict decrease of
`θ = thetaOf b` (with `θ(1) = 0`) and are not repeated. The rate is `ℝ≥0∞`-valued with `e^{−∞} = 0`. -/
theorem bound_J_n (b : ℝ → ℝ) (hθa : StrictAntiOn (thetaOf b) (Set.Icc 0 1))
    (hθ0 : thetaOf b 0 ≤ 1) (n : ℕ) [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hmean : prophetMean μ n = 1) :
    Jn n b (rateOf μ n (thetaOf b)) ≤ expectedReward (thetaOf b) μ n := by sorry

end MeanOnlyProphet
