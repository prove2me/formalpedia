-- Prove2me | Theorems.Thm_HedgePSNV_Supplement_theorem_ec_2
-- name    : HedgePSNV.Supplement.theorem_ec_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:58:41.819521+00:00
-- url     : https://prove2.me/theorems/be8e2990-cfc4-5356-a4f2-810698b3a717
-- title:
--   Theorem EC.2 (corrected: $\mathbb P^M\ne\mathbb P$) — general operational payoff: optimal hedge (EC.10.4)–(EC.10.5) and minimal variance (EC.10.6)
-- statement:
--   Throughout, the general model of §EC.5 holds: the asset model of §3.1 ($B$, $X$, $\mu$, $\sigma$, $\mathcal F\supseteq\mathcal G$, $Z$, $\mathbb P^M$) with a $K$-dimensional Brownian motion $\tilde B$ independent of $B$, $J$ operational factors $A_T=C_T+\tilde\Sigma\tilde B_T$ (EC.5.1) with $C$ adapted to $\mathcal G$ and increments driven by $X$, decisions $q\in\mathbb R^n$ with $q\ge0$, and an operational payoff $H_T(q,a)$.
--
--   Suppose Assumptions 4–5 hold, $Z_T$ is not almost surely equal to $1$, and $H_T(q,A_T)\in L^2(\mathbb P)$ for every $q\ge0$. Fix $m\in\mathbb R$ and $q\ge0$, a representation $V_t(q)=V_0(q)+\int_0^t\xi_s\,dX_s+\int_0^t\delta_s\cdot d\tilde B_s$ (EC.10.2) with $\delta$ a $K$-vector, and a $\mathcal G$-adapted $\zeta$ with $Z^M_t=Z^M_0+\int_0^t\zeta\,dX$ (16).
--   1. The optimal trading strategy of (EC.5.4) is
--   $$
--   \theta^*_t(q)=-\xi_t(q)-\frac{\zeta_t}{Z^M_t}\big[\lambda_m-V_t(q)-\chi^*_t\big],\qquad \lambda_m=\frac{mZ^M_0-V_0(q)}{Z^M_0-1}\qquad(\text{EC.10.4})\text{–}(\text{EC.10.5}),
--   $$
--   with $\chi^*=\int\theta^*dX$: there is an admissible $(\theta^*,\chi^*)$ satisfying (EC.10.4) for a.e. $t\in[0,T]$ a.s., meeting $\mathbb E[H_T(q,A_T)+\chi^*_T]=m$ and attaining $B(m,q)$, and every admissible strategy that meets the constraint and attains $B(m,q)$ has the same terminal gains.
--   2. The optimal value is
--   $$
--   B(m,q)=\frac{[m-V_0(q)]^2}{Z^M_0-1}+\int_0^T\mathbb E\Big[\frac{Z_t}{Z^M_t}\|\delta_t(q)\|^2\Big]dt\qquad(\text{EC.10.6}),
--   $$
--   the squared investment risk plus the squared unhedgeable risk. In particular $Z^M_0=\mathbb E(Z_T^2)>1$ and $0\le Z_t/Z^M_t\le1$ almost surely for each $t\le T$.
--
--   It extends the published Theorem 1(i)–(ii) from the newsvendor payoff to a general payoff with vector noise; its second term is the unhedgeable risk of Assumption EC.2.
--
--   **Formalization Note** $\delta$ is the integrand of the representation (unique up to null sets), not the gradient formula (EC.10.3), whose differentiability the paper does not establish; $\|\delta\|^2=\sum_k\delta_k^2$. $B$ lives in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: §EC.5 keeps the asset model of §3.1 (“the asset price model is the same”, p.ec61) → the published base conventions for the asset model: augmented filtrations, the simple Markov property under $\mathbb P$ and $\mathbb P^M$, the pathwise Itô relation, processes on $\mathbb R_{\ge0}$; reason: the asset model is unchanged; its formalization is the published one, field by field
--   - reading: $\tilde B_t$ a $K$-dimensional standard Brownian motion independent of $B_t$ (p.ec14) → $K$ independent standard real Brownian coordinates, jointly independent of $B$ (path-valued); reason: the definition of a $K$-dimensional standard Brownian motion
--   - reading: each $C_{jt}$ adapted to the filtration of $B$; $C_v-C_u$ adapted to $\sigma\{X_t,u\le t\le v\}$; “$C_t$ … is a $K$-dimensional stochastic process” (p.ec14) → $C$ is $\mathbb R^J$-valued, $\mathcal G$-adapted, with $C_v-C_u$ measurable w.r.t. $\sigma\{X_t:u\le t\le v\}$ for $u\le v\le T$; reason: $A_T=C_T+\tilde\Sigma\tilde B_T\in\mathbb R^J$ forces $C$ to be $J$-dimensional (the printed $K$ is a typo); “adapted” for one random variable means measurable
--   - encoding: $\mathrm{Var}[H_T(q,A_T)]$ in (EC.5.3)–(EC.5.4), presupposed finite → the hypothesis $H_T(q,A_T)\in L^2(\mathbb P)$ for every $q\ge0$ (`PayoffL2`); $H_T(q,\cdot)$ Borel; reason: the analogue of the published `NegPartL2`; it excludes only the case where (EC.5.4) is undefined
--   - encoding: $B(m,q)$ the minimum in (EC.5.4) → an infimum in $[0,\infty]$ of the extended variance (`GenModel.Bval`, field by field the published `Bval`); reason: an empty feasible set gives $+\infty$
--   - reading: Theorem EC.2 prints no hypotheses (“The methodology … leading to Theorem 1 directly applies … the asset price model is the same”, p.ec61) → Theorem 1's hypotheses: Assumptions 4–5 and the standing asset model, for a decision $q\ge0$; reason: the theorem is proved by Theorem 1's method, which uses them (Table EC.3)
--   - correction: “(Note: $Z^M_0=\mathbb E(Z_T^2)>1$.)” with no non-degeneracy hypothesis → the added hypothesis that $Z_T$ is not almost surely $1$ ($\mathbb P^M\ne\mathbb P$); reason: counterexample: $\mu\equiv0$ gives $Z\equiv1$, $Z^M_0=1$, so “$>1$” fails and $\lambda_m$ and (EC.10.6) divide by zero; as in the published Theorem 1(i)–(ii)
--   - reading: “The optimal trading strategy is (EC.10.4)”, $\xi_t,\delta_t$ of (EC.10.2)–(EC.10.3) and $\zeta_t$ of (16) → for every representation $(\xi,\delta)$ and every $\zeta$: existence of an admissible pair satisfying the feedback formula, meeting the constraint and attaining $B$, plus uniqueness of the optimal terminal gains; reason: as the published Theorem 1(i); the stronger reading
--   - reading: $\delta_t(q)=\nabla'_af(t,X_t,A_t,\sigma_t)\tilde\Sigma$ (EC.10.3) in $\|\delta_t(q)\|^2$ → the $d\tilde B$-integrand $\delta$ of the representation (EC.10.2), $\|\delta\|^2=\sum_k\delta_k^2$; reason: (EC.10.3) presupposes a differentiability of $f$ the paper never establishes; when it holds it is this integrand (uniqueness of the representation)
--   - encoding: $0\le Z_t/Z^M_t\le1$ → almost surely, for each $t\le T$; reason: both sides are random variables
--   - encoding: an admissible strategy $\vartheta=\{\theta_t\}$ with $\chi_t(\vartheta)=\int_0^t\theta_sdX_s$ (EC.7.15) → a pair $(\theta,\chi)$ with $\chi$ an $\mathcal F$-adapted version of the gains on $[0,T]$; integrands progressively measurable; reason: the stochastic integral is fixed only up to null sets, so the strategy is carried with its gains (published `AX`)
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Theorem EC.2 and (EC.10.1)–(EC.10.6), p.ec59 (PDF 95); proof p.ec61 (PDF 97)

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_GenHedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

/-- Theorem EC.2, arXiv:2201.01026v4, p.ec59 (corrected: `P^M ≠ P`, as the published Theorem
1(i)–(ii)), for the general operational model of §EC.5 and a decision `q ≥ 0`:
(i) the optimal trading strategy of the hedging problem (EC.5.4) is
`θ*_t(q) = −ξ_t(q) − (ζ_t/Z^M_t)[λ_m − V_t(q) − χ*_t]` (EC.10.4),
`λ_m = (mZ^M_0 − V_0(q))/(Z^M_0 − 1)` (EC.10.5) (Note: `Z^M_0 = E(Z_T²) > 1`);
(ii) the optimal objective function value is
`B(m,q) = [m − V_0(q)]²/(Z^M_0 − 1) + ∫_0^T E[(Z_t/Z^M_t)‖δ_t(q)‖²] dt` (EC.10.6);
in particular `Z^M_0 = E(Z_T²) > 1` and `0 ≤ Z_t/Z^M_t ≤ 1`.

Precisely: for every `m`, every representation (EC.10.2) of `V(q)` with integrands `(ξ, δ)`
(`δ` a `K`-vector) and every `G`-adapted `ζ` with `Z^M_t = Z^M_0 + ∫_0^t ζ dX` (16), there is an
admissible `(θ*, χ*) ∈ A_X` satisfying the feedback equation (EC.10.4) for almost every
`t ∈ [0, T]` almost surely, meeting the mean constraint, attaining `B(m,q)`, and such that every
admissible strategy that meets the constraint and attains `B(m,q)` has the same terminal gains;
and (EC.10.6) holds with this `δ`.

**Formalization Note** The theorem prints no hypotheses; its proof says the methodology of
Theorem 1 "directly applies … the asset price model is the same" (p.ec61), so it carries
Theorem 1's hypotheses (Assumptions 4–5, the standing asset model) and, as the published Theorem
1(i)–(ii), the non-degeneracy `P^M ≠ P`: with `µ ≡ 0` (`Z ≡ 1`) "`Z^M_0 = E(Z_T²) > 1`" fails
and (EC.10.5) divides by zero. `PayoffL2` (`H_T(q, A_T) ∈ L²(P)` for `q ≥ 0`) is the
finite-variance presupposition of (EC.5.4). `δ` is the `dB̃`-integrand of the representation
(unique up to null sets), not the gradient formula (EC.10.3); `‖δ‖² = Σ_k δ_k²`. `B(m,q)` lives
in `ℝ≥0∞`. -/
theorem theorem_ec_2 {n J K : ℕ} (g : GenParams n J K) {Ω : Type*} [MeasurableSpace Ω]
    (M : GenModel g Ω) (hM : M.Standing) (hL2 : M.PayoffL2) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hne : ¬ (M.Z g.T =ᵐ[M.P] fun _ => (1 : ℝ)))
    (m : ℝ) (q : Fin n → ℝ) (hq : 0 ≤ q)
    (ξ χξ L : ℝ≥0 → Ω → ℝ) (δ : ℝ≥0 → Ω → (Fin K → ℝ)) (hξ : IsStronglyProgressive M.F ξ)
    (hδ : IsStronglyProgressive M.F δ) (hχξ : M.IsXGains ξ χξ) (hL : M.IsBtIntegral δ L)
    (hrepV : ∀ t : ℝ≥0, t ≤ g.T → M.V q t =ᵐ[M.P] fun ω => M.V0 q + χξ t ω + L t ω)
    (ζ χζ : ℝ≥0 → Ω → ℝ) (hζ : IsStronglyProgressive M.G ζ) (hχζ : M.IsXGains ζ χζ)
    (hrepZ : ∀ t : ℝ≥0, t ≤ g.T → M.ZM t =ᵐ[M.P] fun ω => M.ZM0 + χζ t ω) :
    (∃ θ χ : ℝ≥0 → Ω → ℝ, (θ, χ) ∈ M.AX ∧
      (∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) (g.T : ℝ))), ∀ᵐ ω ∂M.P,
        θ u.toNNReal ω = -ξ u.toNNReal ω - ζ u.toNNReal ω / M.ZM u.toNNReal ω *
          ((m * M.ZM0 - M.V0 q) / (M.ZM0 - 1) - M.V q u.toNNReal ω - χ u.toNNReal ω)) ∧
      ∫ ω, (M.Hq q ω + χ g.T ω) ∂M.P = m ∧
      evariance (fun ω => M.Hq q ω + χ g.T ω) M.P = M.Bval m q ∧
      ∀ θ' χ' : ℝ≥0 → Ω → ℝ, (θ', χ') ∈ M.AX → ∫ ω, (M.Hq q ω + χ' g.T ω) ∂M.P = m →
        evariance (fun ω => M.Hq q ω + χ' g.T ω) M.P = M.Bval m q →
        χ' g.T =ᵐ[M.P] χ g.T) ∧
    M.Bval m q = ENNReal.ofReal ((m - M.V0 q) ^ 2 / (M.ZM0 - 1)) + M.unhedgeableRiskSq δ ∧
    M.ZM0 = ∫ ω, M.Z g.T ω ^ 2 ∂M.P ∧ 1 < M.ZM0 ∧
    ∀ t : ℝ≥0, t ≤ g.T → ∀ᵐ ω ∂M.P, 0 ≤ M.Z t ω / M.ZM t ω ∧ M.Z t ω / M.ZM t ω ≤ 1 := by sorry

end HedgePSNV.Supplement
