-- Prove2me | Theorems.Thm_ManyServerFluid_Uniqueness_theorem_4_1
-- name    : ManyServerFluid.Uniqueness.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:46.327431+00:00
-- url     : https://prove2.me/theorems/df3fff27-9f40-4c86-a38c-9cbd09e95f33
-- title:
--   Theorem 4.1 — the age equation (4.2) holds iff ν̄ has the representation (4.3)
-- statement:
--   Let $\{\bar\nu_s\}_{s\ge0} \in \mathcal D_{\mathcal M[0,M)}[0,\infty)$ be a vaguely càdlàg path of Radon measures on $[0,M)$ such that for every $m \in [0,M)$ and $T \in [0,\infty)$ there is $C(m,T) < \infty$ with
--   $$\Big|\int_0^\infty\langle\varphi(\cdot,s)h(\cdot),\bar\nu_s\rangle ds\Big| \le C(m,T)\|\varphi\|_\infty \qquad (4.1)$$
--   for every $\varphi \in \mathcal C_c([0,M)\times[0,\infty))$ with support in $[0,m]\times[0,T]$. Let $\upsilon_0 \in \mathcal M[0,M)$ and $Z \in BV_0[0,\infty)$. Then $\bar\nu$ satisfies the age equation (4.2) for $\upsilon_0$ and $Z$ if and only if for every $f \in \mathcal C_c(\mathbb R_+)$ and $t \ge 0$
--   $$\int_{[0,M)} f(x)\,\bar\nu_t(dx) = \int_{[0,M)} f(x+t)\frac{1-G(x+t)}{1-G(x)}\,\upsilon_0(dx) + \int_{[0,t]} f(t-s)\big(1-G(t-s)\big)\,dZ(s). \qquad (4.3)$$
--   Moreover, if $\upsilon_0$ is finite, the age equation implies (4.3) for every $f \in \mathcal C_b(\mathbb R_+)$.
--
--   This is the explicit solution of the transport equation with killing rate $h$ and boundary input $dZ$: mass present initially ages and survives with the conditional probability $(1-G(x+t))/(1-G(x))$, and mass entering at time $s$ survives to age $t-s$ with probability $1-G(t-s)$. Substituting $\upsilon_0 = \bar\nu_0$ and $Z = \bar K$ gives the representation (3.11) of fluid solutions.
--
--   **Formalization Note.** $\upsilon_0$ is any Radon measure on $[0,M)$; nothing ties it to $\bar\nu_0$ (Remark 4.2). $f \in \mathcal C_c(\mathbb R_+)$ is represented by a continuous compactly supported $f$ on $\mathbb R$ and $f \in \mathcal C_b(\mathbb R_+)$ by a bounded continuous function on $\mathbb R$; only values on $[0,\infty)$ are read. $Z = Z_1 - Z_2$ with $Z_i \in \mathcal I_0$. The integrals in (4.2) are taken in $x$ for each $s$, then in $s$ over $[0,t]$.
-- source:
--   Kaspi and Ramanan, Law of Large Numbers Limits for Many-Server Queues, Ann. Appl. Probab. 21(1) (2011), p. 51, Theorem 4.1

import Mathlib
import Definitions.Def_ManyServerFluid_Uniqueness_Model
import Definitions.Def_ManyServerFluid_Uniqueness_AgeEquation
open MeasureTheory Filter Topology Set
open scoped ENNReal BoundedContinuousFunction

namespace ManyServerFluid.Uniqueness

/-- Theorem 4.1, p. 51: for a vaguely càdlàg path ν of Radon measures on [0, M) satisfying (4.1),
any υ_0 ∈ M[0, M) and Z = Z₁ − Z₂ ∈ BV_0[0, ∞), the age equation (4.2) holds iff the
representation (4.3) holds for every f ∈ C_c(R₊) and t ≥ 0; if moreover υ_0 is finite, (4.2)
gives (4.3) for every f ∈ C_b(R₊). -/
theorem theorem_4_1 (S : ServiceLaw) (ν : ℝ → Measure ℝ) (hν : S.IsVagueCadlag ν)
    (hh : S.HazardBound ν) (υ0 : Measure ℝ) (hυ0 : S.IsRadonAges υ0)
    (Z₁ Z₂ : ℝ → ℝ) (hZ₁ : ServiceLaw.IsI0 Z₁) (hZ₂ : ServiceLaw.IsI0 Z₂) :
    (S.AgeEq υ0 Z₁ Z₂ ν ↔
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → ∀ t, 0 ≤ t →
        ∫ x, f x ∂(ν t) = S.ageRep υ0 Z₁ Z₂ f t) ∧
    (IsFiniteMeasure υ0 → S.AgeEq υ0 Z₁ Z₂ ν →
      ∀ f : ℝ →ᵇ ℝ, ∀ t, 0 ≤ t → ∫ x, f x ∂(ν t) = S.ageRep υ0 Z₁ Z₂ f t) := by sorry

end ManyServerFluid.Uniqueness
