-- Prove2me | Theorems.Thm_InsiderDonations_proposition_1
-- name    : InsiderDonations.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:55.3746+00:00
-- url     : https://prove2.me/theorems/ec357d83-e6ec-496b-97ad-673580ec7e5f
-- title:
--   Proposition 1, pp.5–6 — the unique linear stock market equilibrium
-- statement:
--   Under the standing assumptions and $\tau_o>0$, a linear profile is an equilibrium if and only if
--
--   1. the quantity traded by informed trader $j$ is
--   $$
--   x_j^*=\frac{[\bar v-v][(1+m)\tau_o-m(1-\tau_c)]}{[1+m+n]\lambda^*\tau_o};
--   $$
--   2. the quantity donated by informed donor $i$ is
--   $$
--   d_i^*=\frac{[\bar v-v][(1+m)\tau_o-m(1-\tau_c)]}{[1+m+n]\lambda^*\omega\tau_o}-\frac{v[(1-\tau_c)/\tau_o-1]}{\lambda^*\omega}+\frac{\psi_i+\bar\psi}{2\lambda^*\omega\tau_o};
--   $$
--   3. the market-clearing stock price is $P^*=\alpha^*-\lambda^*y$, where
--   $$
--   \alpha^*=\frac{m\bar\psi}{\tau_o}+\frac{[(1+m)\tau_o-m(1-\tau_c)]\bar v}{\tau_o},\qquad
--   \lambda^*=\frac{\sqrt{4\sigma_v^2[(1+m)\tau_o-m(1-\tau_c)][m(1-\tau_c)+n\tau_o]-m[1+m+n]^2\sigma_\psi^2}}{2[1+m+n]\sigma_u\tau_o}.
--   $$
--
--   So the equilibrium exists and is unique among linear profiles. It is the substrate of every comparative static in the paper, including Proposition 3.
--
--   **Formalization Note** Equilibrium is the predicate of the definition item: optimality of every trader and donor for every realization, and $P=E[v\mid y]$ almost surely. Positivity of $\lambda$, symmetry and the formulas are conclusions, not assumptions.
--
--   Differences from the source:
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $m=1$, $n=10$, $\tau_o=-1$, $\tau_c=-2$, $\sigma_\psi=0$, $\sigma_v=\sigma_u=1$ every printed assumption holds, the printed $\lambda^*$ is negative, and no equilibrium exists
--   - reading: "the stock market equilibrium is as follows" (equilibrium never defined beyond the agents' maximization and break-even pricing, p.5; linear pricing in the proof) → a linear profile is an equilibrium (all traders and donors optimal for every realization, $P=E[v\mid y]$ a.s.) if and only if it is the displayed one; reason: this is the Kyle linear equilibrium the proof computes; the iff states existence and uniqueness
--   - encoding: $\tilde v$, $\tilde u$, $\tilde\psi_i$ independent normals → the product of `gaussianReal` laws on $\mathbb R\times\mathbb R\times\mathbb R^m$; reason: same joint law
--   - encoding: each agent's expectation given her information ($v$ for a trader, $(v,\psi_i)$ for a donor) → an integral over the product law of $(u,\psi)$ with that information fixed; reason: $v$, $u$ and the motives are independent, so the two coincide
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Proposition 1, pp.5–6 (PDF pp.7–8); model §2, pp.3–4

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- Proposition 1. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), Proposition 1, pp.5–6:
the stock market equilibrium is
(a) `x_j* = [v̄ − v][(1+m)τo − m(1−τc)]/([1+m+n]λ*τo)`;
(b) `d_i* = [v̄ − v][(1+m)τo − m(1−τc)]/([1+m+n]λ*ωτo) − v[(1−τc)/τo − 1]/(λ*ω) + (ψ_i + ψ̄)/(2λ*ωτo)`;
(c) `P* = α* − λ*y` with `α* = mψ̄/τo + [(1+m)τo − m(1−τc)]v̄/τo` and
`λ* = √(4σv²[(1+m)τo − m(1−τc)][m(1−τc) + nτo] − m[1+m+n]²σψ²)/(2[1+m+n]σuτo)`.

**Formalization Note.** "The equilibrium is as follows" is read as: a linear profile is an
equilibrium (`IsLinEq`) if and only if it is the displayed one, which gives existence and
uniqueness among linear profiles. `0 < τo` is the reading "tax rates are nonnegative". -/
theorem proposition_1 {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo)
    (s : Profile m n) :
    IsLinEq P s ↔
      (∀ j v, trade s j v = (P.vbar - v) * P.A / ((1 + m + n) * lamStar P * P.τo)) ∧
      (∀ i v ψ, donate s i v ψ =
        (P.vbar - v) * P.A / ((1 + m + n) * lamStar P * P.omega * P.τo) -
          v * ((1 - P.τc) / P.τo - 1) / (lamStar P * P.omega) +
          (ψ + P.ψbar) / (2 * lamStar P * P.omega * P.τo)) ∧
      s.α = alphaStar P ∧ s.lam = lamStar P := by sorry

end InsiderDonations
