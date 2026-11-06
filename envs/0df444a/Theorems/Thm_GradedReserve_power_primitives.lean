-- Prove2me | Theorems.Thm_GradedReserve_power_primitives
-- name    : GradedReserve.power_primitives
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:32.405439+00:00
-- url     : https://prove2.me/theorems/abd4f8b0-91ae-48be-915a-439fd17d42bb
-- title:
--   Section A.5 — power-law primitives $Q=v^m$, $H=v^\ell/\ell$, $\varphi f=(k+1)v^k-1$, $r^*=(k+1)^{-1/k}$
-- statement:
--   Let $F(v)=v^k$ on $[0,1]$ with real $k\ge1$, and $n\ge2$; write $m=k(n-1)$, $\ell=m+1$, $N=kn$. Then the density $f(v)=kv^{k-1}$ is a value density in the sense of Section 2, $F$ is regular, $F(v)=v^k$ on $[0,1]$, and
--   $$R_0=R_n(0)=\frac{n(k+1)}{N+1}-\frac n\ell,\qquad Q(v)=v^m,\qquad H(v)=\frac{v^\ell}\ell,$$
--   $$\varphi(v)f(v)=(k+1)v^k-1\ (0<v\le1),\qquad r^*=(k+1)^{-1/k},\qquad D(b)=\frac N{N+1}\,b^{N+1}\ (0\le b\le1).$$
--
--   These identities reduce all objects of Lemma 3.2 to powers, which is what makes the optimum explicit.
--
--   Differences from the source:
--   - encoding: F(v) = v^k with k ≥ 1 → powerDensity k (density k v^{k−1} on [0,1]); k real, Real.rpow; reason: the same law for every real k ≥ 1
--   - encoding: R_n(r) = n ∫_r^1 φ Q f → n ∫_r^1 (v f(v) − (1 − F(v))) Q(v) dv; reason: equal wherever f > 0, i.e. almost everywhere; avoids x/0 = 0
--   - generalization: the identities R₀, Q, H, φf, r*, D for F(v) = v^k → also: powerDensity k is a value density, is regular, and has F(v) = v^k on [0,1]; reason: Section 3 assumes F regular and Theorem 3.1 applies it to F = v^k; dropping these conclusions gives the printed identities
--   - encoding: φ(v)f(v) = (k+1)v^k − 1 → stated for v ∈ (0,1]; reason: at v = 0 with k > 1, f(0) = 0 and φ(0) is undefined
--   - encoding: Q(v) = v^m, H(v) = v^ℓ/ℓ, D(b) = N/(N+1) b^{N+1} → stated for v, b ∈ [0,1]; reason: values and bids lie in [0,1], where the law lives
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section A.5, proof of Theorem 3.1, p.18 (PDF 19)

import Mathlib
import Definitions.Def_GradedReserve_IsRegular
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_lossD
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_oppCdfInt
import Definitions.Def_GradedReserve_powL
import Definitions.Def_GradedReserve_powM
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_rStar
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_valueCdf
import Definitions.Def_GradedReserve_virtualValue
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Power-law primitives** (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section A.5, proof of Theorem 3.1, p.18, PDF 19): for
`F(v) = v^k` with `k ≥ 1` and `n ≥ 2`, `R₀ = R_n(0) = n(k+1)/(N+1) − n/ℓ`, `Q(v) = v^m`,
`H(v) = v^ℓ/ℓ`, `φ(v) f(v) = (k+1) v^k − 1`, `r* = (k+1)^{−1/k}` and `D(b) = (N/(N+1)) b^{N+1}`.
The power law satisfies Section 3's standing assumptions (a value density, regular).

**Formalization Note.** The power law is given by its density `k v^{k−1}` on `[0, 1]`; the first
three conclusions say it is a value density, regular, with `F(v) = v^k`. `φ f` is evaluated on
`(0, 1]`, where `f > 0`. -/
theorem power_primitives (k : ℝ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    IsValueDensity (powerDensity k) ∧ IsRegular (powerDensity k) ∧
    (∀ v ∈ Icc (0:ℝ) 1, valueCdf (powerDensity k) v = v ^ k) ∧
    revCurve (powerDensity k) n 0 = n * (k + 1) / (powN k n + 1) - n / powL k n ∧
    (∀ v ∈ Icc (0:ℝ) 1, oppCdf (powerDensity k) n v = v ^ powM k n) ∧
    (∀ v ∈ Icc (0:ℝ) 1, oppCdfInt (powerDensity k) n v = v ^ powL k n / powL k n) ∧
    (∀ v ∈ Ioc (0:ℝ) 1,
      virtualValue (powerDensity k) v * powerDensity k v = (k + 1) * v ^ k - 1) ∧
    rStar (powerDensity k) = (k + 1) ^ (-1 / k) ∧
    (∀ b ∈ Icc (0:ℝ) 1,
      lossD (powerDensity k) n b = powN k n / (powN k n + 1) * b ^ (powN k n + 1)) := by sorry

end GradedReserve
