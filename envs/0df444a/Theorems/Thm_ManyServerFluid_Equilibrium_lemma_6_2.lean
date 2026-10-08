-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_lemma_6_2
-- name    : ManyServerFluid.Equilibrium.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:37.01226+00:00
-- url     : https://prove2.me/theorems/d2ef5d1f-5e72-40c3-83cf-53fd6a875ae2
-- title:
--   Lemma 6.2 — the reference system π_t of (6.5)–(6.6) converges weakly to ⟨1, π_0⟩ν̄*, (6.7)
-- statement:
--   Let $\pi_0\in\mathcal M_{\le1}[0,M)$, let $U$ be the renewal measure of $G$, and define
--   $$Z(t)=\int_{[0,t]}\Big(\int_{[0,M)}\frac{G(x+t-s)-G(x)}{1-G(x)}\,\pi_0(dx)\Big)dU(s),\qquad t\ge0.\qquad(6.5)$$
--   Then:
--
--   1. $Z\in\mathcal I_0[0,\infty)$: $Z(0)=0$ and $Z$ is nondecreasing and càdlàg;
--   2. there is a càdlàg family $\{\pi_t\}$ of finite measures carried by $[0,M)$ such that, for every bounded continuous $f$ and $t\ge0$,
--   $$\langle f,\pi_t\rangle=\int_{[0,M)}f(x+t)\frac{1-G(x+t)}{1-G(x)}\,\pi_0(dx)+\int_{[0,t]}f(t-s)\big(1-G(t-s)\big)\,dZ(s);\qquad(6.6)$$
--   3. every family $\{\pi_t\}$ satisfying (6.6) satisfies, for every bounded continuous $f$,
--   $$\lim_{t\to\infty}\langle f,\pi_t\rangle=\langle\mathbf 1,\pi_0\rangle\langle f,\bar\nu_*\rangle.\qquad(6.7)$$
--
--   $\{\pi_t\}$ is the age measure of a reference system in which entries into service balance departures, so its total mass is constant; it is the law of the backward recurrence time of a renewal process with interarrival law $G$ started from $\pi_0$. The lemma is the renewal-theoretic input of Theorem 3.9(2). No moment condition beyond the mean (2.2) is assumed.
--
--   **Formalization Note** The paper says "$Z\in\mathcal I_0$ and $\{\pi_t\}\in\mathcal D_{\mathcal M_F}[0,\infty)$ are defined as follows"; parts 1 and 2 state that these definitions are well posed, and part 3 is (6.7) for any family satisfying (6.6) (by (6.6) such a family is unique). The paper's test functions are $f\in\mathcal C_b[0,M)$; here they are bounded continuous functions on $\mathbb R$. Because $\pi_t$ and $\bar\nu_*$ are carried by $[0,M)$, weak convergence against $\mathcal C_b(\mathbb R)$ and against $\mathcal C_b[0,M)$ coincide for such measures, and the restrictions to $[0,\infty)$ of $\mathcal C_b(\mathbb R)$ determine (6.6). $dZ$ is the Lebesgue–Stieltjes measure of $Z$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), pp. 107–108, Lemma 6.2, (6.5)–(6.7)

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Lemma 6.2 (pp. 107–108): Z of (6.5) lies in I_0[0, ∞); a càdlàg family {π_t} of measures on
[0, M) satisfying (6.6) exists; and every family satisfying (6.6) has ⟨f, π_t⟩ → ⟨1, π_0⟩⟨f, ν̄*⟩, (6.7). -/
theorem lemma_6_2 (S : ServiceLaw) (pi0 : FiniteMeasure ℝ) (hpi0 : S.IsSubProb pi0) :
    IsI0 (S.Zfun pi0) ∧
    (∃ piMeas : ℝ → FiniteMeasure ℝ, IsCadlag piMeas ∧
      (∀ t, 0 ≤ t → (piMeas t : Measure ℝ) S.Agesᶜ = 0) ∧ S.SatisfiesEq66 pi0 piMeas) ∧
    ∀ piMeas : ℝ → FiniteMeasure ℝ, S.SatisfiesEq66 pi0 piMeas → ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun t => ∫ x, f x ∂(piMeas t : Measure ℝ)) atTop
        (𝓝 ((pi0.mass : ℝ) * ∫ x, f x ∂S.nuStar)) := by sorry

end ManyServerFluid.Equilibrium
