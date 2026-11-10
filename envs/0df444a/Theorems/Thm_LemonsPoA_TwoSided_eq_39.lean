-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_eq_39
-- name    : LemonsPoA.TwoSided.eq_39
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:11:37.896993+00:00
-- url     : https://prove2.me/theorems/1f44d291-4d02-441a-a433-a13ef75ee8a8
-- title:
--   §4, Eq. (39) — first-best upper bound $FB\le(\mu\sqrt{\mathrm{Var}\,x}+\sqrt{\mathrm{Var}\,y})/\sqrt2$
-- statement:
--   Let $I$ be a market instance with $C\ge 0$, $\mu=E[C]<\infty$, $x(\theta),y(\theta)$ integrable under $G$, and suppose the laws of $x(\theta)$ and of $y(\theta)$ under $G$ each have a log-concave density or are constant. Then
--   $$FB=E\big[(C(x(\theta_B)-x(\theta_S))+y(\theta_B)-y(\theta_S))_+\big]\le E\big[C(x(\theta_B)-x(\theta_S))_+\big]+E\big[(y(\theta_B)-y(\theta_S))_+\big],$$
--   $$E\big[C(x(\theta_B)-x(\theta_S))_+\big]=\mu\,E\big[(x(\theta_B)-x(\theta_S))_+\big],$$
--   $$\mu\,E\big[(x(\theta_B)-x(\theta_S))_+\big]+E\big[(y(\theta_B)-y(\theta_S))_+\big]\le\frac{\mu\sqrt{\mathrm{Var}(x(\theta))}+\sqrt{\mathrm{Var}(y(\theta))}}{\sqrt2}.$$
--
--   This bounds the original first-best by the dispersion of preferences.
--
--   Differences from the source:
--   - encoding: joint law of $(C,\Sigma_S,\Sigma_B)$ on $\mathbb R\times S_S\times S_B$, independent of the i.i.d. types $\theta_S,\theta_B\sim G$ → finite measures $F(\sigma_S,\sigma_B)(A)=\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ of total mass $1$; expectations against $F(\sigma_S,\sigma_B)\otimes G\otimes G$ summed over signal pairs; reason: every law on $\mathbb R\times S_S\times S_B$ with finite $S_S,S_B$ is uniquely of this form; same instances
--   - generalization: (39) is derived under Definition 4.1 / 5.2 (joint log-concave density of $(x,y)$, convex order, rarity, correlation) → only $C\ge 0$, $E[C]<\infty$, $x,y$ integrable, and each marginal law of $x(\theta)$, $y(\theta)$ log-concave or constant; reason: the paper's derivation uses only these ("since the two marginal distributions are log-concave"); a joint log-concave density has log-concave marginals (Prékopa), and in the constant-coordinate case one marginal is a point mass, so it specializes to the paper's setting
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 23, §4, Eq. (39) (in the proof of Theorem 4.2)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Distributions

open MeasureTheory ProbabilityTheory

namespace LemonsPoA.TwoSided

/-- §4, Eq. (39) (p. 23): if `C ≥ 0` with `µ = E[C] < ∞` and the marginal laws of `x(θ)` and
`y(θ)` are log-concave (or constant), then
`FB ≤ E[C (x(θ_B) - x(θ_S))_+] + E[(y(θ_B) - y(θ_S))_+]`,
`E[C (x(θ_B) - x(θ_S))_+] = µ E[(x(θ_B) - x(θ_S))_+]`, and
`µ E[(x(θ_B) - x(θ_S))_+] + E[(y(θ_B) - y(θ_S))_+] ≤ (µ √Var x(θ) + √Var y(θ)) / √2`. -/
theorem eq_39 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hC0 : M.lawC (Set.Iio 0) = 0) (hC : Integrable id M.lawC)
    (hx : Integrable M.x M.G) (hy : Integrable M.y M.G)
    (hlx : LogConcaveOrConst (M.G.map M.x)) (hly : LogConcaveOrConst (M.G.map M.y)) :
    M.FB ≤ M.expect (fun c _ _ θS θB => c * max (M.x θB - M.x θS) 0) +
        ∫ z, max (M.y z.2 - M.y z.1) 0 ∂(M.G.prod M.G) ∧
      M.expect (fun c _ _ θS θB => c * max (M.x θB - M.x θS) 0) =
        M.meanC * ∫ z, max (M.x z.2 - M.x z.1) 0 ∂(M.G.prod M.G) ∧
      M.meanC * ∫ z, max (M.x z.2 - M.x z.1) 0 ∂(M.G.prod M.G) +
          ∫ z, max (M.y z.2 - M.y z.1) 0 ∂(M.G.prod M.G) ≤
        (M.meanC * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G)) /
          Real.sqrt 2 := by sorry

end LemonsPoA.TwoSided
