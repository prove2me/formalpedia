-- Prove2me | Theorems.Thm_HedgePSNV_Supplement_lemma_ec_13
-- name    : HedgePSNV.Supplement.lemma_ec_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:57:34.003155+00:00
-- url     : https://prove2.me/theorems/0558dcef-e424-4f79-a891-d77b9d4f468e
-- title:
--   Lemma EC.13 (corrected: $V_0$ continuous along coordinates at $q_i=0$) — hedged optimal decisions lie below the smallest risk-neutral maximizer $q^{*M}$ when $m\ge V_0(0)$
-- statement:
--   Throughout, the general model of §EC.5 holds: the asset model of §3.1 ($B$, $X$, $\mu$, $\sigma$, $\mathcal F\supseteq\mathcal G$, $Z$, $\mathbb P^M$) with a $K$-dimensional Brownian motion $\tilde B$ independent of $B$, $J$ operational factors $A_T=C_T+\tilde\Sigma\tilde B_T$ (EC.5.1) with $C$ adapted to $\mathcal G$ and increments driven by $X$, decisions $q\in\mathbb R^n$ with $q\ge0$, and an operational payoff $H_T(q,a)$.
--
--   Suppose $H_T(q,A_T)\in L^2(\mathbb P)$ for $q\ge0$, Assumptions 4–5 hold, $H_T$ satisfies Assumption EC.1, and for a family $\delta(q)$ of $d\tilde B$-integrands of representations (EC.10.2) of $V(q)$ the unhedgeable risk satisfies Assumption EC.2 (strictly increasing). Suppose also that for every $q\ge0$ and every $i$, $t\mapsto V_0(q_1,\dots,q_{i-1},t,q_{i+1},\dots,q_n)$ is continuous on $[0,\infty)$. Let
--   $$
--   q^{*M}=\min\arg\max_{q\ge0}\mathbb E^M[H_T(q,A_T)]\qquad(\text{EC.10.9})
--   $$
--   be the least maximizer of $V_0$ over $q\ge0$, and $S^h_m=\arg\min_{q\ge0}B(m,q)$ (EC.10.10). Then for every $m\ge\mathbb E^M[H_T(0,A_T)]$,
--   $$
--   q^h_m\le q^{*M}\qquad\text{for every }q^h_m\in S^h_m\text{ with }B(m,q^h_m)<\infty .
--   $$
--
--   With Theorem EC.3 (which gives $q^{*M}\le q^*$ under positive impact) it yields Theorem EC.1.
--
--   **Formalization Note** The printed lemma is false without the continuity premise; see DISPROOF.md. Concavity in each coordinate (Assumption EC.1(i)) already gives continuity at interior points, so the premise excludes only jumps of $V_0$ at the faces $q_i=0$.
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
--   - correction: Lemma EC.13 for every payoff satisfying Assumptions EC.1–EC.2 and every $m\ge\mathbb E^M[H_T(0,A_T)]$ → the added premise that $t\mapsto V_0(q\text{ with }q_i:=t)$ is continuous on $[0,\infty)$ for every $q\ge0$ and every $i$; reason: counterexample: $n=J=K=1$, $C\equiv0$, $\tilde\Sigma=1$, $H(q,a)=h(q)+qa$ with $h(0)=-10$, $h(q)=1-(q-1)^2$ for $q>0$ satisfies Assumptions EC.1–EC.2 ($\Psi(q)=q^2\int_0^T\mathbb E[Z_t/Z^M_t]dt$), $q^{*M}=1$, $m=-5\ge V_0(0)$, and for $Z^M_0$ near $1$ every minimizer of $B(m,\cdot)$ lies near $1+\sqrt6>q^{*M}$; the proof's intermediate-value steps (pp.ec64–ec65) use exactly this continuity
--   - encoding: $q^h_m\in S^h_m=\arg\min_{q\ge0}B(m,q)$ (problem (EC.5.4) presupposed feasible) → every minimizer $q\ge0$ with $B(m,q)<\infty$; reason: if $\mathbb P^M=\mathbb P$ and $m$ exceeds every attainable $V_0$, no hedge meets the constraint and every $q$ would minimize $B\equiv\infty$; the finiteness excludes exactly that case (as in the published Lemma EC.7)
--   - encoding: $q^{*M}=\min\arg\max_{q\ge0}\mathbb E^M[H_T(q,A_T)]=\min\arg\max_{q\ge0}\mathbb E[H_T(q,A^M_T)]$ (EC.10.9) → the first form, $V_0(q)=\mathbb E^M[H_T(q,A_T)]$; reason: $A^M_T$ has under $\mathbb P$ the law of $A_T$ under $\mathbb P^M$, so the two forms are the same set
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Lemma EC.13 and (EC.10.9)–(EC.10.10), p.ec63 (PDF 99); proof pp.ec63–ec65 (PDF 99–101)

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_GenHedging
import Definitions.Def_HedgePSNV_Supplement_PayoffAssumptions

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

/-- Lemma EC.13, arXiv:2201.01026v4, p.ec63 (corrected: `V_0` continuous along coordinate
lines of the orthant), in the setting of Theorem EC.1 (Assumptions EC.1–EC.2, the general model
of §EC.5 with Assumptions 4–5): let `q*M := min arg max_{q ≥ 0} E^M[H_T(q, A_T)]` (EC.10.9) and
`S^h_m = arg min_{q ≥ 0} B(m, q)` (EC.10.10). Then, for any `m ≥ E^M[H_T(0, A_T)]`,
`q^h_m ≤ q*M` for all `q^h_m ∈ S^h_m`.

Precisely: `q*M` is the least element of the set of maximizers of `V_0(q) = E^M[H_T(q, A_T)]`
over `q ≥ 0`; `δ q` is the `dB̃`-integrand of a representation of `V(q)` for each `q ≥ 0`,
and Assumption EC.2 holds for it (strict reading); `q ≥ 0` is any minimizer of `B(m, ·)` over
the orthant with `B(m, q) < ∞`. Added premise: for every `q ≥ 0` and every coordinate `i`,
`t ↦ V_0(q with qᵢ := t)` is continuous on `[0, ∞)`.

**Formalization Note** Correction: the printed lemma is false when `V_0` jumps at a face
`qᵢ = 0` of the orthant, which Assumption EC.1(i) (concavity on `qᵢ ≥ 0`) allows. With `n = J =
K = 1`, `C ≡ 0`, `Σ̃ = 1`, `H(q,a) = h(q) + qa`, `h(0) = −10` and `h(q) = 1 − (q − 1)²` for
`q > 0`, every assumption holds (the unhedgeable risk is `q²∫_0^T E[Z_t/Z^M_t] dt`, strictly
increasing), `q*M = 1`, and for `m = −5` and `Z^M_0` close to `1` every minimizer of `B(m, ·)`
lies near `1 + √6 > q*M`. The proof's intermediate-value steps (p.ec64: "there exists
q̃ ∈ [0, q*M] such that V_0(q̃) = m"; p.ec65) use exactly the added continuity; concavity
already gives it at interior points, so only jumps at the faces `qᵢ = 0` are excluded. The
finiteness `B(m, q) < ∞` excludes only the degenerate case `P^M = P` with `m` above every
attainable `V_0`, where problem (EC.5.4) has no feasible hedge and every `q` would minimize
`B ≡ ⊤` (as in the published Lemma EC.7). `PayoffL2` is the finite-variance presupposition of
(EC.5.4). The second form of (EC.10.9), with `A^M_T` (the `P`-version of the `P^M`-law of
`A_T`), is the same quantity. -/
theorem lemma_ec_13 {n J K : ℕ} (g : GenParams n J K) {Ω : Type*} [MeasurableSpace Ω]
    (M : GenModel g Ω) (hM : M.Standing) (hL2 : M.PayoffL2) (h4 : M.Assumption4)
    (h5 : M.Assumption5) (hEC1 : AssumptionEC1 g.H)
    (δ : (Fin n → ℝ) → ℝ≥0 → Ω → (Fin K → ℝ))
    (hδ : ∀ q : Fin n → ℝ, 0 ≤ q → M.IsBtIntegrand q (δ q)) (hEC2 : M.AssumptionEC2 δ)
    (hcont : ∀ q : Fin n → ℝ, 0 ≤ q → ∀ i : Fin n,
      ContinuousOn (fun t : ℝ => M.V0 (Function.update q i t)) (Set.Ici 0))
    (qM : Fin n → ℝ) (hqM : IsLeast (orthantArgmax M.V0) qM)
    (m : ℝ) (hm : M.V0 0 ≤ m) (q : Fin n → ℝ) (hq : 0 ≤ q)
    (hmin : ∀ q' : Fin n → ℝ, 0 ≤ q' → M.Bval m q ≤ M.Bval m q')
    (hfin : M.Bval m q < ⊤) :
    q ≤ qM := by sorry

end HedgePSNV.Supplement
