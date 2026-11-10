-- Prove2me | Theorems.Thm_MultiInterm_Compete_lemma_C_1
-- name    : MultiInterm.Compete.lemma_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:40:46.532381+00:00
-- url     : https://prove2.me/theorems/3ca7c7bb-7daf-4844-930c-3c15a8538b94
-- title:
--   Lemma C.1 — two transformed reserve revenues exceed the threshold revenue
-- statement:
--   Let $n\ge3$, and let $D$ be an atomless regular value distribution with support $[0,\bar v]$, allowing $\bar v=\infty$. Write $F$ for its CDF, $g(x)=xF(x)^{n-1}$, and $R$ for the reserve-revenue formula of Definition 6.5. For $0<\tau<\bar v$ and $x,y\in(0,\tau]$, if
--   $$x+y\ge\frac{4\tau F(\tau)^{n-1}}{1+F(\tau)^{n-1}},$$
--   then
--   $$R(g(x))+R(g(y))>R(\tau).$$
--   This is a distributional inequality independent of the composite game or any equilibrium. The hypotheses on $n$, $D$ and $\tau$ are inherited from the surrounding proof of Lemma 6.8.
--
--   Differences from the source:
--   - encoding: nonnegative real values and reserves; bidders 1 through n; intermediaries A and B → nonnegative-real carriers, Fin n bidders, and Bool intermediaries (false=A, true=B); reason: these are relabelings of the same spaces; the support endpoint may still be infinite
--   - encoding: atomless regular D on [0, v̄] → the referenced regular continuous component, full interval support, and zeroMass=0; reason: this specifies the same density and virtual-value convention with no finite-mean condition
--   - encoding: the density formula for R with integration from τ to v̄ → the same nonnegative integrand integrated against D over (τ,∞), valued in extended nonnegative reals; reason: dD=f(v)dv away from zero and D vanishes beyond its support; the omitted zero endpoint contributes zero
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), p. 44 (PDF 45), Lemma C.1; proof pp. 44–46 (PDF 45–47)

import Definitions.Def_MultiInterm_Compete_ValueDistribution

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

theorem lemma_C_1 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (τ x y : ℝ≥0) (hτ : 0 < τ) (hτv : (τ : ℝ≥0∞) < D.upper)
    (hx : 0 < x ∧ x ≤ τ) (hy : 0 < y ∧ y ≤ τ)
    (hxy : 4 * τ * D.F τ ^ (n - 1) / (1 + D.F τ ^ (n - 1)) ≤ x + y) :
    R D n τ < R D n (g D n x) + R D n (g D n y) := by sorry

end MultiInterm.Compete
