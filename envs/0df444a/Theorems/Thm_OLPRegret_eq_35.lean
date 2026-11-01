-- Prove2me | Theorems.Thm_OLPRegret_eq_35
-- name    : OLPRegret.eq_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:05:17.101099+00:00
-- url     : https://prove2.me/theorems/05ddf6a3-8155-4747-bea9-3c93113822b9
-- title:
--   (35) — the regret of Algorithm 2 is at most the sum of myopic regrets (corrected: terms selected by the realized decision)
-- statement:
--   Under Algorithm 2, run with any map $y$ in place of $b\mapsto y_\infty^b$, for every sample of customers with $u_s,a_s\ge0$, every $\delta>0$, every choice of shadow prices and every $T_0\ge0$,
--   $$
--   \bar R_n=\bar V_n^\beta-\bar v_n\le\sum_{t=T_0+1}^n r_t+\sum_{s\le T_0}u_s,
--   $$
--   where $r_t$ is the upper myopic regret. At $T_0=0$ this reads $\bar R_n\le\sum_{t=1}^nr_t$.
--
--   Differences from the source:
--   - correction: the $r_t$ of (35), with terms selected by $\Delta_t(y_\infty^{b_t})>0$ or $\le0$ → terms selected by $x_t=1$ or $0$; reason: (33) is false when $\Delta_t(y_\infty^{b_t})>0$ and $a_t\not\le tb_t$, since the linear program can still accept a fraction. Counterexample under all assumptions: $m=1$, $u\sim\mathrm{Uniform}[0,1]$, $a\equiv1$, $\beta=1/2$, $n=1$, $u_1=3/4$: then $x_1=0$, $\bar R_1=3/8$, and the printed $r_1=\Delta_1(y_0)^-=0$ with $y_0=0$
--   - generalization: "for sufficiently small $\delta>0$"; the sum over $t=1,\dots,n$ → every $\delta>0$ and every $T_0$, the periods up to $T_0$ being charged their utilities; reason: the derivation uses no smallness of $\delta$, $T_0=0$ gives (35), and Lemma 4's threshold needs the general form
--   - reading: $y_t^b$, a not-necessarily-unique minimizer → every minimizer; reason: the proofs use only the minimizing property, so this is the strong reading
--   - reading: $y_0$ undefined at $t=1$ → $y_0=0$; reason: (30) at $t=1$ reads $xa'y_0\le 0$ for every bundle, which forces $y_0=0$
--   - generalization: Algorithm 2 with the limiting shadow prices $y_\infty^{b_t}$ → Algorithm 2 run with an arbitrary map $y$ (no hypothesis); reason: once the terms are selected by the realized decision, the derivation (31)–(34) never uses the value of $y$, and $y=y_\infty$ is a special case
--   - encoding: (35) for the random customers, which satisfy Assumption 2 almost surely → pathwise for every sample with $u_s,a_s\ge0$; reason: samples violating Assumption 2 are null
--   - encoding: periods counted backward, $t=n,\dots,1$ → the index $t$ of `Fin n` holds period $t+1$, and the stock $tb_t$ is tracked with $b_t$ recovered by division; reason: Lean convention; same instances
-- source:
--   Bray, arXiv:1912.08917v6, (35), p.27; (31)–(34), pp.26–27

import Mathlib
import Definitions.Def_OLPRegret_regret
import Definitions.Def_OLPRegret_algorithm2
import Definitions.Def_OLPRegret_myopicRegret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, (35), p.27 (corrected): pathwise under Algorithm 2,
`R̄ₙ ≤ Σ_{t=T₀+1}^n rₜ + Σ_{s≤T₀} uₛ`, which at `T₀ = 0` is `R̄ₙ ≤ Σₜ rₜ`.

**Formalization Note** `rₜ` is `rUpper`, which selects its term by the realized decision. The bound
holds for every sample of nonnegative customers, every `δ > 0`, every selection `y` and every choice
`Y` of shadow prices. The extra `T₀` lets early periods be bounded by their utilities, which the
threshold in `OLPRegret.lemma_4` needs. -/
theorem eq_35 {m n : ℕ} (β : E m) (hβ : VNonneg β) (y : E m → E m) (δ : ℝ) (hδ : 0 < δ)
    (ω : Sample m n) (hω : ∀ s, 0 ≤ (ω s).1 ∧ VNonneg (ω s).2)
    (Y : ℕ → E m → E m) (hY : IsShadowPriceChoice ω Y) (T₀ : ℕ) :
    offlineLP ω β - onlineValue (algorithm2 y) β ω ≤
      (∑ t : Fin n with T₀ < period t, rUpper δ (algorithm2 y) β Y ω t) +
        ∑ s : Fin n with period s ≤ T₀, (ω s).1 := by sorry

end OLPRegret
