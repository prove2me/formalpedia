-- Prove2me | Theorems.Thm_GRH_grh_implies_primeCountingAP
-- name    : GRH.grh_implies_primeCountingAP
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T17:51:10.494383+00:00
-- url     : https://prove2.me/theorems/45677104-5a7e-42c5-a05c-0b8ca6f135ac
-- title:
--   GRH $\Rightarrow$ $\pi(x; q, a) = \mathrm{Li}(x)/\varphi(q) + O(x^{1/2+\varepsilon})$
-- statement:
--   Assume the **generalized Riemann hypothesis** in the mission's zero-free form: $L(s,\chi) \ne 0$ whenever $\operatorname{Re}(s) > 1/2$, for every modulus $q \ge 1$ and every Dirichlet character $\chi$ modulo $q$, except the principal-character pole at $s = 1$.
--
--   Let $q \ge 1$, let $a$ satisfy $\gcd(a, q) = 1$, and let $\varepsilon > 0$. Then
--
--   $$\pi(x;\, q, a) \;=\; \frac{\operatorname{Li}(x)}{\varphi(q)} \;+\; O\bigl(x^{1/2+\varepsilon}\bigr) \qquad (x \to \infty),$$
--
--   where $\pi(x; q, a)$ counts the primes $p \le x$ with $p \equiv a \pmod q$, $\operatorname{Li}(x) = \int_2^x \frac{dt}{\log t}$ is the offset logarithmic integral, $\varphi$ is Euler's totient function, and the implied constant may depend on $q$, $a$ and $\varepsilon$ but not on $x$.
--
--   This is the effective prime number theorem for arithmetic progressions under GRH: a considerable strengthening of the unconditional theorem, with square-root cancellation in the error term. For $q = 1$ it recovers the RH-conditional estimate for $\pi(x)$.
--
--   **Formalization Note.** The error is expressed with `Asymptotics.IsBigO` along `atTop` on $\mathbb{R}$. The counting function is `GRH.primeCountingAP`; $\operatorname{Li}$ reuses the published `LandauFunction.logIntegral`; $\varphi(q)$ is `Nat.totient`, cast to $\mathbb{R}$ (nonzero since $q \ne 0$). The modulus $q = 0$ is excluded by hypothesis.
-- source:
--   https://en.wikipedia.org/wiki/Generalized_Riemann_hypothesis (section 'Consequences of GRH', effective Dirichlet theorem item: 'If the generalized Riemann hypothesis is true, then for every ε > 0: π(x,a,d) = Li(x)/φ(d) + O(x^{1/2+ε}) as x→∞', with Li(x) = ∫₂ˣ dt/ln t; oldid 1378052002).

import Mathlib
import Definitions.Def_GRH_Defs
import Definitions.Def_LandauFunction_logIntegral

open Filter Asymptotics

namespace GRH

theorem grh_implies_primeCountingAP
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0)
    (q a : ℕ) (hq : q ≠ 0) (ha : a.Coprime q) (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => (primeCountingAP q a x : ℝ) - LandauFunction.logIntegral x / (q.totient : ℝ))
      =O[atTop] (fun x : ℝ => x ^ ((1 : ℝ) / 2 + ε)) := by
  sorry

end GRH
