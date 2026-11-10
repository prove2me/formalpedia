-- Prove2me | Theorems.Thm_LRTempElim_theorem_2
-- name    : LRTempElim.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T03:27:15.076663+00:00
-- url     : https://prove2.me/theorems/66345400-a0d5-46d0-ae06-e28c6db85b04
-- title:
--   Theorem 2: $C_{\mathrm{path}}(a)=O(1+a^6)$, $C_{\mathrm{NCE}}(a)=\Omega(a^5e^{a^2/8})$, ratio $\to0$, and both are leading mean-risk coefficients
-- statement:
--   Let $Q_a=N(-a/2,1)$, $P_a=N(a/2,1)$, $\nu_a=\tfrac12(P_a+Q_a)$, $\ell^\star(x)=ax$ and $\phi(x)=(1,x,x^2)^\top$, with sampling units $W=(X_0,X_1)\sim Q_a\otimes P_a$. Let $C_{\mathrm{path}}(a)=\operatorname{tr}(\Sigma_{\nu_a}\mathrm{Var}_W\Psi_a(W))$ be the covariance-defined coefficient of the continuous path-moment estimator (influence function (51), including the inverse-moment term) and $C_{\mathrm{NCE}}(a)=\operatorname{tr}(\Sigma_{\nu_a}H_a^{-1}\mathrm{Var}_W(g_a(W))H_a^{-1})$ that of balanced logistic DRE (eq. (52)). Then:
--
--   0. for every $a$, $\Psi_a(W)$ and $g_a(W)$ are square-integrable, so both coefficients are finite covariance traces;
--   1. $C_{\mathrm{path}}(a)=O(1+a^6)$ as $a\to\infty$: there are $C,A$ with $C_{\mathrm{path}}(a)\le C(1+a^6)$ for all $a\ge A$;
--   2. $C_{\mathrm{NCE}}(a)=\Omega(a^5e^{a^2/8})$ as $a\to\infty$: there are $c>0$ and $A$ with $C_{\mathrm{NCE}}(a)\ge c\,a^5e^{a^2/8}$ for all $a\ge A$;
--   3. consequently $C_{\mathrm{path}}(a)/C_{\mathrm{NCE}}(a)\to0$ as $a\to\infty$;
--   4. these are the leading mean-risk coefficients, at each fixed $a$ as $n\to\infty$: for every estimator sequence $\hat\theta_n$ on a probability space $(\Omega,P)$ for which $\sqrt n(\hat\theta_n-c_a)$ converges in distribution to $N(0,V_a)$ (the regular fixed-$a$ local central limit theorem) and $n\|\hat\theta_n-c_a\|^2$ is uniformly integrable,
--   $$
--   n\,\mathbb E_P\big[\|\phi^\top\hat\theta_n-\ell^\star\|^2_{L^2(\nu_a)}\big]\longrightarrow C(a),
--   $$
--   where $(c_a,V_a,C(a))=(m_a,V_{\mathrm{path}}(a),C_{\mathrm{path}}(a))$ for the path estimator, with $m_a=\int_0^1M_t^{-1}b_t\,dt$ its population head, and $(c_a,V_a,C(a))=(\theta^\star_a,V_{\mathrm{NCE}}(a),C_{\mathrm{NCE}}(a))$, $\theta^\star_a=(0,a,0)^\top$, for balanced logistic DRE.
--
--   Under weak overlap the logistic coefficient grows like $a^5e^{a^2/8}$ while the path coefficient grows at most polynomially, so at a common calibrated target the path estimator's first-order risk is exponentially smaller for large separation.
--
--   **Formalization Note** The limits in clause 4 take $n\to\infty$ at each fixed $a$; clauses 1–3 concern the $n$-free coefficients. The norm on $\mathbb R^3$ is Euclidean.
--
--   Differences from the source:
--   - generalization: (11) and the ratio limit under the assumed local CLTs → clauses 1–3 stated without any CLT hypothesis; reason: the coefficients are covariance-defined, explicit Gaussian integrals (§A.2.3); the CLTs enter only the mean-risk clause
--   - generalization: "the continuous path-moment estimator and balanced logistic estimator" satisfying the local CLT and the uniform-integrability condition → clause 4 for every estimator sequence on every probability space with these two properties; reason: the paper's two estimators are such sequences by assumption
--   - reading: "the regular fixed-a local central limit theorems" → √n(θ̂_n − c_a) converges in distribution to N(0, V_a), centred at the population target (m_a for the path estimator, θ⋆_a = (0, a, 0) for logistic DRE), with V_a = Var_W Ψ_a(W) resp. H_a⁻¹S_aH_a⁻¹; reason: §A.2.3 defines these covariances as the asymptotic ones; centring the path CLT at m_a does not presuppose its calibration (Proposition A.2)
--   - reading: "these are the leading mean-risk coefficients" → n · E_P‖ϕ⊤θ̂_n − ℓ⋆‖²_{L²(ν_a)} → C(a) for each fixed a; reason: eq. (10), the meaning given just before the theorem
--   - encoding: O(1 + a⁶) and Ω(a⁵e^{a²/8}) as a → ∞ → ∃ C A, ∀ a ≥ A, C_path(a) ≤ C(1 + a⁶) and ∃ c > 0, ∃ A, ∀ a ≥ A, c·a⁵e^{a²/8} ≤ C_NCE(a); reason: eventual bounds with existential constants over real a (Knuth's Ω)
--   - encoding: the uniform-integrability condition above → `UniformIntegrable (fun n ω => n‖θ̂_n ω − c_a‖²) 1 P`; reason: Mathlib's uniform integrability with p = 1 on a probability space
--   - encoding: finite covariance-defined coefficients (implicit) → clause 0: Ψ_a(W) and g_a(W) are in L²(Q_a ⊗ P_a); reason: a conclusion, not a hypothesis; it excludes Lean's junk value 0 for the covariance of a non-integrable or non-measurable map
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Theorem 2, eq. (11), p.7 (pdf p.9), with §4.1 and eq. (10), p.7, and §A.2.3 eqs. (51)–(52), p.20 (pdf p.22)

import Mathlib
import Definitions.Def_LRTempElim_PathEstimator
import Definitions.Def_LRTempElim_Logistic

open MeasureTheory ProbabilityTheory Matrix Filter Topology

universe u

namespace LRTempElim

/-- **Theorem 2** (Polynomial–exponential risk separation under weak overlap). Chen, Wu, Yang,
Zeng, *Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), Theorem 2, eq. (11), p.7 (pdf p.9), with
the setting of §4.1 and eq. (10) (p.7) and the coefficient definitions of §A.2.3 (p.20, pdf p.22).

"For the Gaussian family, features and sample budget above, assume the regular fixed-a local
central limit theorems for the continuous path-moment estimator and balanced logistic estimator.
As `a → ∞`, their covariance-defined function-risk coefficients satisfy
`C_path(a) = O(1 + a⁶)`, `C_NCE(a) = Ω(a⁵e^{a²/8})`. (11) Consequently `C_path(a)/C_NCE(a) → 0`.
Under the uniform-integrability condition above, these are the leading mean-risk coefficients.
The limits take `n → ∞` at each fixed a before examining increasing separation."

**Formalization Note.**
* Family `Q_a = N(−a/2, 1)`, `P_a = N(a/2, 1)`, `ν_a = (P_a + Q_a)/2`, `ℓ⋆(x) = ax`, features
  `ϕ = (1, x, x²)` (`phi3`, 0-based), one sampling unit `W = (X₀, X₁) ∼ Q_a ⊗ P_a` (`pairLaw a`).
* The coefficients are the covariance-defined ones of §A.2.3: `C_path(a) = tr(Σ_{ν_a} Var_W Ψ_a(W))`
  with the path influence function `Ψ_a` of eq. (51) (`Cpath phi3 a`), and
  `C_NCE(a) = tr(Σ_{ν_a} H_a⁻¹ (Var_W g_a(W)) H_a⁻¹)` with the pair gradient of eq. (52)
  (`Cnce a`). They are explicit Gaussian integrals; clauses (0)–(3) need no CLT hypothesis.
* Clause (0): for every `a`, `Ψ_a(W)` and `g_a(W)` are in `L²(Q_a ⊗ P_a)` (in particular
  measurable), so both covariance matrices are genuine finite covariances.
* `O` and `Ω` are eventual bounds as `a → +∞` over real `a`, with existential constants
  (Knuth's `Ω`): clauses (1), (2). Clause (3) is the ratio limit.
* Clause (4) is "these are the leading mean-risk coefficients" through eq. (10), for every fixed
  `a`, for each estimator: for every probability space `(Ω, P)` and every estimator sequence
  `θ̂_n : Ω → ℝ³` (Euclidean norm) such that `√n(θ̂_n − c_a)` converges in distribution to
  `N(0, V_a)` (the regular fixed-`a` local CLT, centred at the estimator's population target:
  `c_a = m_a = ∫₀¹ M_t⁻¹b_t dt` for the path estimator, `c_a = θ⋆_a = (0, a, 0)` for logistic DRE)
  and `n‖θ̂_n − c_a‖²` is uniformly integrable, `n · E_P‖ϕ⊤θ̂_n − ℓ⋆‖²_{L²(ν_a)} → C(a)`
  (that is, `C(a)/n + o(n⁻¹)`). The limit is in `n` at each fixed `a`. -/
theorem theorem_2 :
    -- (0) the two covariances are genuine: `Ψ_a(W)` and `g_a(W)` are square-integrable
    (∀ a : ℝ,
      MemLp (fun W => WithLp.toLp 2 (influence phi3 a W) : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
          2 (pairLaw a) ∧
        MemLp (fun W => WithLp.toLp 2 (logisticGrad (fun x => Real.sigmoid (a * x)) phi3 W) :
          ℝ × ℝ → EuclideanSpace ℝ (Fin 3)) 2 (pairLaw a)) ∧
    -- (1) `C_path(a) = O(1 + a⁶)` as `a → ∞`
    (∃ C A : ℝ, ∀ a ≥ A, Cpath phi3 a ≤ C * (1 + a ^ 6)) ∧
    -- (2) `C_NCE(a) = Ω(a⁵ e^{a²/8})` as `a → ∞`
    (∃ c > (0 : ℝ), ∃ A : ℝ, ∀ a ≥ A, c * (a ^ 5 * Real.exp (a ^ 2 / 8)) ≤ Cnce a) ∧
    -- (3) `C_path(a) / C_NCE(a) → 0`
    Tendsto (fun a => Cpath phi3 a / Cnce a) atTop (𝓝 0) ∧
    -- (4) leading mean-risk coefficients, for every fixed `a`
    (∀ a : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (θhat : ℕ → Ω → EuclideanSpace ℝ (Fin 3)),
      -- (4a) continuous path-moment estimator, centred at `m_a`, covariance `V_path(a)`
      (TendstoInDistribution
          (fun (n : ℕ) ω => Real.sqrt n • (θhat n ω - WithLp.toLp 2 (readout phi3 a))) atTop id
          (fun _ => P) (multivariateGaussian 0 (Vpath phi3 a)) →
        UniformIntegrable
          (fun (n : ℕ) ω => (n : ℝ) * ‖θhat n ω - WithLp.toLp 2 (readout phi3 a)‖ ^ 2) 1 P →
        Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, risk a (WithLp.ofLp (θhat n ω)) ∂P) atTop
          (𝓝 (Cpath phi3 a))) ∧
      -- (4b) balanced logistic DRE, centred at `θ⋆_a`, covariance `V_NCE(a)`
      (TendstoInDistribution
          (fun (n : ℕ) ω => Real.sqrt n • (θhat n ω - WithLp.toLp 2 (thetaStar a))) atTop id
          (fun _ => P) (multivariateGaussian 0 (Vnce a)) →
        UniformIntegrable
          (fun (n : ℕ) ω => (n : ℝ) * ‖θhat n ω - WithLp.toLp 2 (thetaStar a)‖ ^ 2) 1 P →
        Tendsto (fun n : ℕ => (n : ℝ) * ∫ ω, risk a (WithLp.ofLp (θhat n ω)) ∂P) atTop
          (𝓝 (Cnce a)))) := by sorry

end LRTempElim
