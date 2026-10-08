-- Prove2me | Theorems.Thm_ManyServerFluid_Equilibrium_proposition_6_1_1
-- name    : ManyServerFluid.Equilibrium.proposition_6_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:00.057052+00:00
-- url     : https://prove2.me/theorems/48e62b5b-8e83-43a9-bc37-2c0f31e08ae5
-- title:
--   Proposition 6.1(1) — from empty, ⟨1, ν̄_t⟩ = X̄(t) = ∫_0^t (1 − G(t − s)) λ̄(s) ds on [0, τ_1), and the limit of ⟨f, ν̄_t⟩ as t ↑ τ_1
-- statement:
--   Suppose Assumption 2 holds. Let $\bar E(t)=\int_0^t\bar\lambda(s)\,ds$ for $t\ge0$ with $\bar\lambda$ locally integrable, let $(\bar E,0,\tilde{\mathbf 0})\in\mathcal S_0$ (the system starts empty), and let $(\bar X,\bar\nu)$ solve the associated fluid equations. Let
--   $$\tau_1=\inf\Big\{t>0:\int_0^t(1-G(t-s))\,\bar\lambda(s)\,ds=1\Big\}\qquad(6.1)$$
--   with $\inf\emptyset=\infty$. Then:
--
--   1. for every $t\in[0,\tau_1)$,
--   $$\langle\mathbf 1,\bar\nu_t\rangle=\bar X(t)=\int_0^t(1-G(t-s))\,\bar\lambda(s)\,ds;$$
--   2. if $\tau_1<\infty$, then for every bounded continuous $f$, as $t\uparrow\tau_1$,
--   $$\langle f,\bar\nu_t\rangle\to\int_0^{\tau_1}f(\tau_1-s)\big(1-G(\tau_1-s)\big)\,\bar\lambda(s)\,ds.$$
--
--   Before the servers first fill up, no customer waits, so each arrival enters service at once and the age measure is explicit: it has density $x\mapsto(1-G(x))\bar\lambda(t-x)$ on $[0,t]$.
--
--   **Formalization Note** The paper prints the limit as $\int_0^{\tau_1}f(t-s)(1-G(t-s))\bar\lambda(s)\,ds$, which contains the moving time $t$ and evaluates $f$ at negative arguments; the statement here has $\tau_1$ in place of $t$, which is what the proof's representation gives at $t=\tau_1$. The limit is stated only for $\tau_1<\infty$ (for $\tau_1=\infty$ "as $t\to\tau_1$" makes no finite-time claim and the proof uses only the finite case). The paper's test functions are $f\in\mathcal C_b(\mathbb R_+)$; here $f$ is a bounded continuous function on $\mathbb R$, an equivalent choice since only $f$ on $[0,\infty)$ is read. Assumption 2 is the standing hypothesis of Section 6. $\tau_1$ is an extended real, and "$t<\tau_1$" compares $t$ in $\overline{\mathbb R}$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), pp. 104–105, §6 standing assumptions, Proposition 6.1(1), (6.1)

import Mathlib
import Definitions.Def_ManyServerFluid_Equilibrium_Model
import Definitions.Def_ManyServerFluid_Equilibrium_Renewal
open MeasureTheory Filter Topology Set BoundedContinuousFunction

namespace ManyServerFluid.Equilibrium

/-- Proposition 6.1(1) (p. 105): from an empty start, before τ_1 the system is below capacity,
⟨1, ν̄_t⟩ = X̄(t) = ∫_0^t (1 − G(t − s)) λ̄(s) ds, and ⟨f, ν̄_t⟩ has the stated limit as t ↑ τ_1 < ∞. -/
theorem proposition_6_1_1 (S : ServiceLaw) (hA2 : S.Assumption2)
    (lam E X : ℝ → ℝ) (ν : ℝ → FiniteMeasure ℝ)
    (hlam_int : ∀ t, IntegrableOn lam (Icc 0 t))
    (hE : ∀ t, 0 ≤ t → E t = ∫ s in Icc 0 t, lam s)
    (hS0 : S.InS0 E 0 0) (hsol : S.IsFluidSolution E 0 0 X ν) :
    (∀ t : ℝ, 0 ≤ t → (t : EReal) < S.tau1 lam →
      ((ν t).mass : ℝ) = X t ∧ X t = ∫ s in Icc 0 t, (1 - S.G (t - s)) * lam s) ∧
    ∀ τ : ℝ, S.tau1 lam = (τ : EReal) → ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun t => ∫ x, f x ∂(ν t : Measure ℝ)) (𝓝[<] τ)
        (𝓝 (∫ s in Icc 0 τ, f (τ - s) * (1 - S.G (τ - s)) * lam s)) := by sorry

end ManyServerFluid.Equilibrium
