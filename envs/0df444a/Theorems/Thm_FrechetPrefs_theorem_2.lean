-- Prove2me | Theorems.Thm_FrechetPrefs_theorem_2
-- name    : FrechetPrefs.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:03.809969+00:00
-- url     : https://prove2.me/theorems/b3711ba5-5c32-4bcc-8845-6e281e8583ff
-- title:
--   Theorem 2, p.11 — quantile minimizer, value (7), limits and expansion (8) of the multiplier utility (corrected: minimum over the floor class; uniform $O$ needs $u'''$ bounded)
-- statement:
--   Let $Q_1,\dots,Q_n\in P_2(\mathbb R)$ and $w\in\Delta^{n-1}$, with Assumption 2: $Q_i((-\infty,K_i])=0$ for constants $K_i>0$. Let $K_B=\sum_iw_iK_i$, let $u$ satisfy Assumption 1, let $Q_B$ be the barycenter, and let $0<K<K_B$. Put
--   $$\theta_c=\max\Big\{|u''(K)|,\ \frac{u'(K)}{K_B-K}\Big\}.$$
--   There is a family $(Q_\theta)$ with quantiles $F_\theta^{-1}$ such that the following hold.
--
--   **(a)** For every $\theta>\theta_c$:
--
--   1. $Q_\theta$ minimizes the objective of problem (4) over the floor class at $K$;
--   2. for all $s\in(0,1)$, $F_\theta^{-1}$ solves equation (5) at $\rho=\theta$, that is $\frac1\theta u'(F_\theta^{-1}(s))+F_\theta^{-1}(s)=F_B^{-1}(s)$, and
--   $$K<F_\theta^{-1}(s)\le F_B^{-1}(s),\qquad F_\theta^{-1}(s)\le F_B^{-1}(s)-\frac1\theta u'(F_B^{-1}(s));$$
--   3. the value satisfies (7),
--   $$U_\theta(X)=\int_0^1u(F_\theta^{-1})\,ds+\frac\theta2\int_0^1(F_\theta^{-1}-F_B^{-1})^2ds=\int_0^1u(F_\theta^{-1})\,ds+\frac1{2\theta}\int_0^1(u'(F_\theta^{-1}))^2ds;$$
--   4. $U_\theta(X)\le\mathbb E_{Q_B}[u(X)]$.
--
--   Moreover, as $\theta\to\infty$, $F_\theta^{-1}\to F_B^{-1}$ uniformly on $(0,1)$ and $U_\theta(X)\to\mathbb E_{Q_B}[u(X)]$.
--
--   **(b)** Assume $u\in C^3$. For each $s\in(0,1)$, there are $C,\Theta$ with
--   $$\Big|F_\theta^{-1}(s)-\Big(F_B^{-1}(s)-\frac1\theta u'(F_B^{-1}(s))+\frac1{\theta^2}u''(F_B^{-1}(s))u'(F_B^{-1}(s))\Big)\Big|\le\frac C{\theta^3}\qquad(\theta\ge\Theta).$$
--   If moreover $u^{(3)}$ is bounded on $[K,\sup_sF_B^{-1}(s))$, then $C,\Theta$ can be chosen independent of $s$, and also
--   $$\big|U_\theta(X)-\mathbb E_{Q_B}[V_\theta(X)]\big|\le\frac C{\theta^3}\qquad(\theta\ge\Theta),\qquad V_\theta(x)=u(x)-\frac{(u'(x))^2}{2\theta}+\frac{(u'(x))^2u''(x)}{2\theta^2}.$$
--
--   The theorem solves the multiplier problem in closed form above an explicit threshold and quantifies how uncertainty aversion acts as additional risk aversion.
--
--   **Formalization Note** For $\theta\le\theta_c$ the family is unconstrained. $U_\theta$ is the infimum of the objective over the floor class, and part (a) shows that it is attained.
--
--   Differences from the source:
--   - correction: "A minimizer Q_θ of problem (4) in P(R)" → the minimum is over the floor class {μ ∈ P₂ : μ((−∞,K)) = 0}; reason: the printed claim is false: for u = log, n = 1, Q₁ = δ₂, K₁ = 1 the objective at ½δ₂ + ½δ_t tends to −∞ as t ↓ 0 for every θ; p.11 and p.ec5 make this restriction themselves
--   - correction: O(1/θ³) in (8) read uniformly in s (Remark EC.3) and integrated into U_θ, with u ∈ C³ only → the uniform bound and the bound on U_θ assume u‴ bounded on [K, sup F_B⁻¹); reason: with u ∈ C³ only they fail for unbounded support: a u with u″ = −b, b piecewise constant with narrow steps at the integers, and Q₁ = Σ 2^{−k} δ_{k+1}; condition (EC.13) names this dependence, and the bound is automatic for bounded F_B⁻¹
--   - generalization: the floor K* = minᵢ Kᵢ, with θ_c dividing by K_B − K* → any floor K with 0 < K < K_B, with threshold max{|u″(K)|, u′(K)/(K_B − K)}; reason: it specializes to K = K* whenever K* < K_B, and it also covers K* = K_B (for example n = 1), where (EC.11) divides by zero
--   - generalization: "there exists a positive constant θc" → the explicit threshold of (EC.11), for all θ above it, which can be 0 when u′(K) = 0 = u″(K); reason: any positive number above it is then the printed constant, so the printed statement follows
--   - generalization: "If u′ is a decreasing function" → no such hypothesis; reason: Assumption 1 implies it (`inada_consequences`), so the printed conclusion is recovered
--   - generalization: continuous quantiles "for simplicity" (p.ec5) → all measures of P₂, with left-continuous quantiles; reason: continuous quantiles are a special case
--   - generalization: F_θ⁻¹ → F_B⁻¹ as θ → ∞ → uniform convergence on (0,1); reason: uniform convergence implies the printed limit
--   - encoding: V_θ(x) = u(x)(1 − (1/2θ)(u′)²/u + (1/2θ²)(u′)²u″/u) + O(1/θ³) → `effectiveUtility` multiplied out, with the O stated as an explicit bound; reason: the printed form divides by u(x), which can vanish; the two agree where u(x) ≠ 0
--   - encoding: O(1/θ³) "for sufficiently large θ" → ∃ C Θ, ∀ θ ≥ Θ, |…| ≤ C/θ³; reason: the definition of the symbol
--   - encoding: Assumption 2: Q_j(X ∈ [0,K_j]) = 0 with X positive → Q_j((−∞,K_j]) = 0 and K_j > 0; reason: the positivity of X is stated on pp.10–11, so the two sets carry the same mass
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - encoding: the 2-Wasserstein metric → W₂ by the quantile formula of eq. (1); reason: eq. (1) is the paper’s own := on p.6
--   - encoding: a lottery X on (Ω,B) under models Q → the law of X, a probability measure on ℝ; reason: the page itself reduces to measures on ℝ on p.5; X plays no other role
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), Theorem 2, p.11; proof in Appendix B, p.27, and Section EC.2.3, pp.ec5–ec7

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Theorem 2, p.11 of Petracou–Xepapadeas–Yannacopoulos, *Decision Making under Model Uncertainty:
Fréchet-Wasserstein Mean Preferences*, manuscript MS-DEC-19-01009-REV, with proof in Appendix B, p.27,
and Section EC.2.3, pp.ec5–ec7.

Under Assumption 1 (`hu`) and Assumption 2 (`hAss2`), for every `θ` above the threshold (EC.11):
`Qθ θ` minimizes problem (4) on the floor class; its quantile `F_θ⁻¹` solves (5) at `ρ = θ` and satisfies
`K < F_θ⁻¹ ≤ F_B⁻¹` and `F_θ⁻¹ ≤ F_B⁻¹ − (1/θ) u′(F_B⁻¹)`; both expressions (7) hold; and
`U_θ(X) ≤ E_{Q_B}[u(X)]`. As `θ → ∞`, `F_θ⁻¹ → F_B⁻¹` uniformly on `(0,1)` and `U_θ(X) → E_{Q_B}[u(X)]`.
If `u` is `C³`, the expansion of `F_θ⁻¹` in (8) holds for each `s`, and if moreover `u‴` is bounded on
`[K, sup F_B⁻¹)`, it holds uniformly in `s` together with the expansion of `U_θ`.

**Formalization Note.** Two printed claims are corrected. (C1) The minimum is over the floor class, not
over all of `P(ℝ)`. (C2) The `O` that is uniform in `s`, and the one on `U_θ`, need the bound on `u‴`.
`K` is any floor in `(0, K_B)`, the paper's being `K*`. `V_θ` is multiplied out as `effectiveUtility`. Quantiles are
read on the open interval. `Qθ θ` is unconstrained for `θ` at or below the threshold. -/
theorem theorem_2 {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ) (Kv : Fin n → ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ) (K : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hAss2 : ∀ i, 0 < Kv i ∧ (Q i : Measure ℝ) (Iic (Kv i)) = 0)
    (hu : IsInadaUtility u) (hB : IsBarycenter w Q B)
    (hK0 : 0 < K) (hK : K < KB w Kv) :
    ∃ Qθ : ℝ → ProbabilityMeasure ℝ,
      (∀ θ, thetaC u K (KB w Kv) < θ →
        Qθ θ ∈ floorClass K ∧
        IsMinOn (objective u w Q B θ) (floorClass K) (Qθ θ) ∧
        (∀ s ∈ Ioo (0 : ℝ) 1,
          1 / θ * deriv u (q (Qθ θ) s) + q (Qθ θ) s = q B s ∧
          K < q (Qθ θ) s ∧ q (Qθ θ) s ≤ q B s ∧
          q (Qθ θ) s ≤ q B s - 1 / θ * deriv u (q B s)) ∧
        multiplierUtility u w Q B θ K =
          ∫ s in Ioo (0 : ℝ) 1, u (q (Qθ θ) s) +
            θ / 2 * ∫ s in Ioo (0 : ℝ) 1, (q (Qθ θ) s - q B s) ^ 2 ∧
        multiplierUtility u w Q B θ K =
          ∫ s in Ioo (0 : ℝ) 1, u (q (Qθ θ) s) +
            1 / (2 * θ) * ∫ s in Ioo (0 : ℝ) 1, (deriv u (q (Qθ θ) s)) ^ 2 ∧
        multiplierUtility u w Q B θ K ≤ ∫ x, u x ∂(B : Measure ℝ)) ∧
      TendstoUniformlyOn (fun θ s => q (Qθ θ) s) (q B) atTop (Ioo 0 1) ∧
      Tendsto (fun θ => multiplierUtility u w Q B θ K) atTop
        (𝓝 (∫ x, u x ∂(B : Measure ℝ))) ∧
      (ContDiffOn ℝ 3 u (Ioi 0) →
        (∀ s ∈ Ioo (0 : ℝ) 1, ∃ C Θ : ℝ, ∀ θ, Θ ≤ θ →
          |q (Qθ θ) s - T2 u θ (q B s)| ≤ C / θ ^ 3) ∧
        ((∃ M : ℝ, ∀ x, K ≤ x → (∃ s ∈ Ioo (0 : ℝ) 1, x ≤ q B s) →
            |deriv (deriv (deriv u)) x| ≤ M) →
          ∃ C Θ : ℝ,
            (∀ s ∈ Ioo (0 : ℝ) 1, ∀ θ, Θ ≤ θ →
              |q (Qθ θ) s - T2 u θ (q B s)| ≤ C / θ ^ 3) ∧
            ∀ θ, Θ ≤ θ →
              |multiplierUtility u w Q B θ K -
                ∫ x, effectiveUtility u θ x ∂(B : Measure ℝ)| ≤ C / θ ^ 3)) := by sorry

end FrechetPrefs
