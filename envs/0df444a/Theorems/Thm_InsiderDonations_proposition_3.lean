-- Prove2me | Theorems.Thm_InsiderDonations_proposition_3
-- name    : InsiderDonations.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:20:52.282106+00:00
-- url     : https://prove2.me/theorems/2c46089a-ad4c-4834-a2f7-b0cd9b5f8af9
-- title:
--   Proposition 3, p.11 — price efficiency $\Omega=[1+m+n]\tau_o/(\sigma_v^2[(1+m)\tau_o-m(1-\tau_c)])$, $d\Omega/dm>d\Omega/dn>0$, $d\Omega/d\tau_o,d\Omega/d\tau_c<0$
-- statement:
--   Consider the market of the definition item: $m\ge1$ insiders who may donate shares, $n\ge0$ informed traders, retail supply $\tilde u\sim N(0,\sigma_u^2)$, and a market maker who sets $P=E[v\mid y]$. Assume the standing assumptions of §2 and $\tau_o>0$. Write price efficiency as $\Omega=1/E[(P-v)^2]$. In equilibrium,
--
--   1. **(a)** price efficiency equals
--   $$
--   \Omega=\frac{[1+m+n]\tau_o}{\sigma_v^2[(1+m)\tau_o-m(1-\tau_c)]};
--   $$
--   precisely, a linear equilibrium exists, and every linear equilibrium has this $\Omega$;
--   2. **(b)** price efficiency increases with market participation, with a more pronounced increase for donors:
--   $$
--   \frac{d\Omega}{dm}>\frac{d\Omega}{dn}>0;
--   $$
--   3. **(c)** price efficiency decreases with tax rates:
--   $$
--   \frac{d\Omega}{d\tau_o}<0\qquad\text{and}\qquad\frac{d\Omega}{d\tau_c}<0 .
--   $$
--
--   Competition among informed participants raises the information content of the price, more so when the added participant is a donor, whose gifts load more heavily on firm value than a trader's orders; higher tax rates weaken that loading.
--
--   **Formalization Note** The derivatives in (b) and (c) are derivatives of the closed form of (a), viewed as a function of real $m,n,\tau_o,\tau_c$, evaluated at the model's parameters.
--
--   Differences from the source:
--   - reading: tax rates (printed assumption $\tau_c\le\tau_o<1/2$ only) → hypothesis $0<\tau_o$; reason: tax rates are nonnegative; with $m=1$, $n=10$, $\tau_o=-1$, $\tau_c=-2$, $\sigma_\psi=0$, $\sigma_v=\sigma_u=1$ every printed assumption holds but no equilibrium exists, so "in equilibrium" would be empty
--   - reading: "In equilibrium, (a) price efficiency $\Omega$ equals …" → a linear equilibrium (all traders and donors optimal for every realization, $P=E[v\mid y]$ a.s.) exists, and every linear equilibrium has $1/E[(P-v)^2]$ equal to the closed form; reason: the paper's equilibrium is Proposition 1's linear one; the existence clause prevents a vacuous statement
--   - reading: $d\Omega/dm$, $d\Omega/dn$ for counts $m,n$ → derivatives of the closed form of (a) in real $m,n$ at $(\uparrow m,\uparrow n)$; reason: the proof (A6) differentiates the closed form; a function of integers has no derivative
--   - encoding: $\tilde v$, $\tilde u$, $\tilde\psi_i$ independent normals → the product of `gaussianReal` laws on $\mathbb R\times\mathbb R\times\mathbb R^m$; reason: same joint law
--   - encoding: each agent's expectation given her information ($v$ for a trader, $(v,\psi_i)$ for a donor) → an integral over the product law of $(u,\psi)$ with that information fixed; reason: $v$, $u$ and the motives are independent, so the two coincide
--   - encoding: σv, σu, σψ, the standard deviations of the normal laws of §2, with no printed sign → σv > 0, σu > 0, σψ ≥ 0 (in the standing assumptions); reason: standard deviations are nonnegative; ṽ and ũ are genuine noise (λ* divides by σu, and with σv = 0 the interior condition fails); σψ = 0 is the degenerate case the paper itself uses in §3.4
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Proposition 3, p.11 (PDF p.13); proof Appendix p.A2 (PDF p.24), (A6); Ω defined p.11

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- Proposition 3. Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), Proposition 3, p.11. In
equilibrium,
(a) price efficiency `Ω` equals `[1+m+n]τo/(σv²[(1+m)τo − m(1−τc)])`;
(b) `dΩ/dm > dΩ/dn > 0`; and
(c) `dΩ/dτo < 0` and `dΩ/dτc < 0`.

**Formalization Note.** "In equilibrium" is read as: a linear equilibrium exists and every linear
equilibrium has `Ω = 1/E[(P − v)²]` equal to the closed form. (b) and (c) are derivatives of the
closed form `OmegaF` in real `m`, `n`, `τo`, `τc`, evaluated at the model's parameters.
`0 < τo` is the reading "tax rates are nonnegative". -/
theorem proposition_3 {m n : ℕ} (P : Params m n) (hP : P.Standing) (hτo : 0 < P.τo) :
    ((∃ s, IsLinEq P s) ∧ ∀ s, IsLinEq P s → priceEff P s = OmegaF m n P.τo P.τc P.σv) ∧
    (deriv (fun x : ℝ => OmegaF x n P.τo P.τc P.σv) m >
        deriv (fun x : ℝ => OmegaF m x P.τo P.τc P.σv) n ∧
      deriv (fun x : ℝ => OmegaF m x P.τo P.τc P.σv) n > 0) ∧
    (deriv (fun t => OmegaF m n t P.τc P.σv) P.τo < 0 ∧
      deriv (fun t => OmegaF m n P.τo t P.σv) P.τc < 0) := by sorry

end InsiderDonations
