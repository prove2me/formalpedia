-- Prove2me | Theorems.Thm_MilnorDynamics_modular_lambda_exists
-- name    : MilnorDynamics.modular_lambda_exists
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T15:51:17.811874+00:00
-- url     : https://prove2.me/theorems/1c8cff88-c9a2-4941-ac35-8e197e88db93
-- title:
--   The modular function $\lambda$: $\mathbb H/\Gamma(2)\cong\mathbb C\setminus\{0,1\}$
-- statement:
--   This is the existence of the elliptic modular function $\lambda$ together with its basic mapping properties.
--
--   Let $\mathbb H=\{\tau\in\mathbb C:\operatorname{Im}\tau>0\}$ be the upper half-plane with the Möbius action of $\mathrm{SL}_2(\mathbb Z)$, and let $\Gamma(2)\subset\mathrm{SL}_2(\mathbb Z)$ be the principal congruence subgroup of level $2$ (matrices congruent to the identity modulo $2$). There is a holomorphic function $\lambda:\mathbb H\to\mathbb C$ such that
--
--   1. $\lambda$ omits the values $0$ and $1$: $\lambda(\tau)\notin\{0,1\}$ for all $\tau\in\mathbb H$;
--   2. $\lambda$ takes every other value: for every $w\in\mathbb C\setminus\{0,1\}$ there is $\tau\in\mathbb H$ with $\lambda(\tau)=w$;
--   3. the fibres of $\lambda$ are exactly the $\Gamma(2)$-orbits: for all $\tau,\tau'\in\mathbb H$,
--   $$
--   \lambda(\tau)=\lambda(\tau')\iff \tau'=\gamma\cdot\tau\ \text{ for some }\gamma\in\Gamma(2).
--   $$
--
--   Equivalently, $\lambda$ is $\Gamma(2)$-invariant and induces a bijection $\mathbb H/\Gamma(2)\to\mathbb C\setminus\{0,1\}$. A classical witness is $\lambda(\tau)=\theta_2(\tau)^4/\theta_3(\tau)^4$, with $\theta_2(\tau)=\sum_{n\in\mathbb Z}e^{\pi i(n+1/2)^2\tau}$ and $\theta_3(\tau)=\sum_{n\in\mathbb Z}e^{\pi i n^2\tau}$.
--
--   This is the analytic half of the construction of the universal covering $\mathbb H\to\mathbb C\setminus\{0,1\}$; combined with the proper discontinuity of the $\Gamma(2)$-action it yields Milnor's Lemma 2.5 for the triply punctured sphere, and hence Montel's theorem.
--
--   **Formalization Note** The function is recorded as $p:\mathbb C\to\mathbb C$, complex differentiable on the open set $\{\operatorname{Im}z>0\}$; only its values on $\mathbb H$ matter. Points of $\mathbb H$ are Mathlib's `UpperHalfPlane`, coerced to $\mathbb C$, and $\gamma\cdot\tau$ is Mathlib's action of `SL(2, ℤ)` on `ℍ`, under which $-I$ acts trivially.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, §2, Lemma 2.5 (The Triply Punctured Sphere), p. 17; L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, Chapter 7, §3.4 (The modular function λ(τ))

import Mathlib

open Set Topology UpperHalfPlane

namespace MilnorDynamics

theorem modular_lambda_exists :
    ∃ p : ℂ → ℂ, DifferentiableOn ℂ p {z : ℂ | 0 < z.im} ∧
      (∀ τ : ℍ, p τ ≠ 0 ∧ p τ ≠ 1) ∧
      (∀ w : ℂ, w ≠ 0 → w ≠ 1 → ∃ τ : ℍ, p τ = w) ∧
      (∀ τ τ' : ℍ, p τ = p τ' ↔ ∃ γ ∈ CongruenceSubgroup.Gamma 2, γ • τ = τ') := by sorry

end MilnorDynamics
