-- Prove2me | Theorems.Thm_HedgePSNV_Supplement_theorem_ec_1
-- name    : HedgePSNV.Supplement.theorem_ec_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:58:11.82658+00:00
-- url     : https://prove2.me/theorems/3413320b-daac-42ee-a650-02c6fcbaf1e7
-- title:
--   Theorem EC.1 — general operational payoff: under positive impact $C^M_T\preceq C_T$, every hedged optimal decision lies below $q^*$
-- statement:
--   Throughout, the general model of §EC.5 holds: the asset model of §3.1 ($B$, $X$, $\mu$, $\sigma$, $\mathcal F\supseteq\mathcal G$, $Z$, $\mathbb P^M$) with a $K$-dimensional Brownian motion $\tilde B$ independent of $B$, $J$ operational factors $A_T=C_T+\tilde\Sigma\tilde B_T$ (EC.5.1) with $C$ adapted to $\mathcal G$ and increments driven by $X$, decisions $q\in\mathbb R^n$ with $q\ge0$, and an operational payoff $H_T(q,a)$.
--
--   Suppose $H_T(q,A_T)\in L^2(\mathbb P)$ for $q\ge0$, Assumptions 4–5 hold, $H_T$ satisfies Assumption EC.1, and for a family $\delta(q)$ of $d\tilde B$-integrands of representations (EC.10.2) of $V(q)$ the unhedgeable risk satisfies Assumption EC.2 (strictly increasing in each component of $q$). Suppose the asset price trend positively impacts the stochastic operational factors, $C^M_T\preceq C_T$ (the $\mathbb P^M$-law of $C_T$ is below its $\mathbb P$-law in the usual multivariate stochastic order). Let
--   $$
--   q^*=\min\arg\max_{q\ge0}\mathbb E[H_T(q,A_T)]\qquad(\text{EC.5.5})
--   $$
--   be the least maximizer, $m=\mathbb E[H_T(q^*,A_T)]$ and $S^h_m=\arg\min_{q\ge0}B(m,q)$. Then
--   $$
--   q\le q^*\qquad\text{for all }q\in S^h_m .
--   $$
--
--   It extends the published Theorem 2 from the price-setting newsvendor to general operational payoffs: hedging lowers the operational decision when the asset trend raises the operational factors.
--
--   Differences from the source:
--   - reading: §EC.5 keeps the asset model of §3.1 (“the asset price model is the same”, p.ec61) → the published base conventions for the asset model: augmented filtrations, the simple Markov property under $\mathbb P$ and $\mathbb P^M$, the pathwise Itô relation, processes on $\mathbb R_{\ge0}$; reason: the asset model is unchanged; its formalization is the published one, field by field
--   - reading: $\tilde B_t$ a $K$-dimensional standard Brownian motion independent of $B_t$ (p.ec14) → $K$ independent standard real Brownian coordinates, jointly independent of $B$ (path-valued); reason: the definition of a $K$-dimensional standard Brownian motion
--   - reading: each $C_{jt}$ adapted to the filtration of $B$; $C_v-C_u$ adapted to $\sigma\{X_t,u\le t\le v\}$; “$C_t$ … is a $K$-dimensional stochastic process” (p.ec14) → $C$ is $\mathbb R^J$-valued, $\mathcal G$-adapted, with $C_v-C_u$ measurable w.r.t. $\sigma\{X_t:u\le t\le v\}$ for $u\le v\le T$; reason: $A_T=C_T+\tilde\Sigma\tilde B_T\in\mathbb R^J$ forces $C$ to be $J$-dimensional (the printed $K$ is a typo); “adapted” for one random variable means measurable
--   - encoding: $\mathrm{Var}[H_T(q,A_T)]$ in (EC.5.3)–(EC.5.4), presupposed finite → the hypothesis $H_T(q,A_T)\in L^2(\mathbb P)$ for every $q\ge0$ (`PayoffL2`); $H_T(q,\cdot)$ Borel; reason: the analogue of the published `NegPartL2`; it excludes only the case where (EC.5.4) is undefined
--   - encoding: $B(m,q)$ the minimum in (EC.5.4) → an infimum in $[0,\infty]$ of the extended variance (`GenModel.Bval`, field by field the published `Bval`); reason: an empty feasible set gives $+\infty$
--   - reading: Theorem EC.1 / Lemma EC.13 state only Assumptions EC.1–EC.2 → also Assumptions 4–5 of the asset model; reason: $B(m,q)$ and the unhedgeable risk are those of Theorem EC.2, whose proof is Theorem 1's (Assumptions 4–5, p.ec61); Table EC.3 lists them for every result built on Theorem 1
--   - reading: Assumption EC.1 (i)–(iv) with decisions “without loss of generality … $q\ge0$” (p.ec14) → all four parts on the orthant $q\ge0$; concavity in each $q_i\ge0$ with the other coordinates fixed; supermodularity with coordinatewise $\vee,\wedge$; reason: decisions are restricted to $q\ge0$ throughout §EC.5
--   - reading: Assumption EC.2: “The unhedgeable risk increases in each component of q” (p.ec16) → strictly: $0\le q\le q'$, $q\ne q'$ imply $\int_0^T\mathbb E[(Z_t/Z^M_t)\|\delta_t(q)\|^2]dt<\int_0^T\mathbb E[(Z_t/Z^M_t)\|\delta_t(q')\|^2]dt$, for $\delta(q)$ the $d\tilde B$-integrand of a representation of $V(q)$; reason: under the weak reading the theorem is false: $H_T(q,a)=h(q)+a_1$ with $h$ concave and flat on $[q^*,q^*+1]$ satisfies Assumption EC.1, its unhedgeable risk is constant, and when $\mathbb E[C_{1,T}]>\mathbb E^M[C_{1,T}]$ the minimizers of $B(m,\cdot)$ include $q^*+1>q^*$; the paper's model case “strictly increases” (p.ec48)
--   - reading: $q^*:=\min\{\arg\max_{q\ge0}\cdot\}$, “there exists a smallest optimal solution … (Topkis 1978)” (p.ec16) → the least maximizer is a hypothesis (`IsLeast (orthantArgmax …)`), not constructed; reason: the existence argument needs compactness the setting lacks; the theorem is about the least maximizer whenever it exists
--   - encoding: $C^M_T\preceq C_T$, i.e. $\mathbb P(C^M_T\in U)\le\mathbb P(C_T\in U)$ for every upper set $U\subseteq\mathbb R^J$ → `MultivariateOrder P^M P C_T C_T` (v2: Borel increasing test functions with finite expectations); reason: $C^M_T$ has under $\mathbb P$ the law of $C_T$ under $\mathbb P^M$ (p.12); for random vectors on probability spaces the function form is the upper-set order with Borel upper sets (Shaked–Shanthikumar (6.B.4))
--   - reading: $S^h_m=\arg\min_{q\ge0}B(m,q)$ → every minimizer $q\ge0$ of $B(m,\cdot)$ over the orthant; no minimizer is asserted to exist; reason: the theorem quantifies over all of $S^h_m$
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Theorem EC.1, p.ec16 (PDF 52); (EC.5.3)–(EC.5.5), pp.ec15–ec16; proof p.ec65 (PDF 101)

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_GenHedging
import Definitions.Def_HedgePSNV_Supplement_PayoffAssumptions
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

/-- Theorem EC.1, arXiv:2201.01026v4, p.ec16: suppose Assumptions EC.1–EC.2 hold and the asset
price trend positively impacts the stochastic operational factors (`C^M_T ⪯ C_T`, or
equivalently `P(C^M_T ∈ U) ≤ P(C_T ∈ U)` for any upper set `U ⊆ ℝᴶ`). Let
`m = E[H_T(q*, A_T)]` and `S^h_m = arg min_{q ≥ 0} B(m, q)`, where `q*` is defined in (EC.5.5).
Then `q ≤ q*` for all `q ∈ S^h_m`.

Precisely: in the general model of §EC.5 (with Assumptions 4–5 and `H_T(q, A_T) ∈ L²(P)`),
`q* := min arg max_{q ≥ 0} E[H_T(q, A_T)]` (EC.5.5) is the least element of the set of
maximizers of `E[H_T(·, A_T)]` over `q ≥ 0`; `δ q` is the `dB̃`-integrand of a representation
of `V(q)` for each `q ≥ 0`, and the unhedgeable risk it defines satisfies Assumption EC.2
(strict reading); every minimizer `q ≥ 0` of `B(m, ·)` over the orthant satisfies `q ≤ q*`.

**Formalization Note** `C^M_T ⪯ C_T` is the published `MultivariateOrder` (v2) between the
`P^M`-law and the `P`-law of `C_T` (`C^M_T` has under `P` the law of `C_T` under `P^M`, p.12),
the paper's upper-set order for random vectors. Assumption EC.2 is read strictly (see
`AssumptionEC2`; under the weak reading the theorem is false). `B(m, q)` and the unhedgeable
risk are those of Theorem EC.2, which shares the asset model of Theorem 1, so the theorem
carries Assumptions 4–5. `q*` is a hypothesis (`IsLeast`), not constructed. No finiteness of
`B` and no `P^M ≠ P` is assumed: the zero hedge makes `B(m, q*)` finite. -/
theorem theorem_ec_1 {n J K : ℕ} (g : GenParams n J K) {Ω : Type*} [MeasurableSpace Ω]
    (M : GenModel g Ω) (hM : M.Standing) (hL2 : M.PayoffL2) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hEC1 : AssumptionEC1 g.H)
    (δ : (Fin n → ℝ) → ℝ≥0 → Ω → (Fin K → ℝ))
    (hδ : ∀ q : Fin n → ℝ, 0 ≤ q → M.IsBtIntegrand q (δ q)) (hEC2 : M.AssumptionEC2 δ)
    (hpos : StochasticOrders.Multivariate.MultivariateOrder M.PM M.P (M.C g.T) (M.C g.T))
    (qs : Fin n → ℝ) (hqs : IsLeast (orthantArgmax fun q => ∫ ω, M.Hq q ω ∂M.P) qs)
    (q : Fin n → ℝ) (hq : 0 ≤ q)
    (hmin : ∀ q' : Fin n → ℝ, 0 ≤ q' →
      M.Bval (∫ ω, M.Hq qs ω ∂M.P) q ≤ M.Bval (∫ ω, M.Hq qs ω ∂M.P) q') :
    q ≤ qs := by sorry

end HedgePSNV.Supplement
