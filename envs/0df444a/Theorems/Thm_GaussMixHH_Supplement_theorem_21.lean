-- Prove2me | Theorems.Thm_GaussMixHH_Supplement_theorem_21
-- name    : GaussMixHH.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:36:39.306293+00:00
-- url     : https://prove2.me/theorems/ce607b50-3b36-40ec-857a-c1cb45eb8192
-- title:
--   Theorem 21, p.29 — a moment-matched pair of separated center distributions whose Gaussian mixtures are $e^{-cH}$-close in total variation
-- statement:
--   There are absolute constants $c,C>0$ such that the following holds. Let $0<\Delta\le1$ and $0<\eta\le e^{-4}$, and put
--
--   $$L:=\log(1/\eta),\qquad H:=\frac{n^{1/3}L^{4/3}}{\Delta^{4/3}} .$$
--
--   Suppose $n\ge CL^2/\Delta^2$. Then there are finitely supported probability distributions $\mathcal D_1,\mathcal D_2$ on $\mathbb R^n$ such that
--
--   1. the distinct centers in each support are at distance at least $\Delta$ from one another;
--   2. $\mathcal D_1(\{0\})=\eta$ and $\mathcal D_2(\{0\})=0$, and every nonzero center in either support has norm at least $\Delta$;
--   3. their homogeneous Gaussian mixtures satisfy
--   $$d_{TV}(\mathcal D_1*\phi_n,\ \mathcal D_2*\phi_n)\le e^{-cH},$$
--   where $\phi_n$ is the density of $N(0,I_n)$ and $d_{TV}(P,Q)=\tfrac12\int|p-q|$.
--
--   Here $\mathcal D*\phi_n$ is the mixture $\mathrm{Mix}(\mathcal D,1)$: draw $\mu\sim\mathcal D$ and output $\mu+Z$ with $Z\sim N(0,I_n)$ independent.
--
--   This is the hard instance behind the lower bound of Theorem 2: one mixture has a center of weight $\eta$ at the origin and the other has none near it, yet the two are exponentially close in total variation, so no algorithm with fewer than about $e^{cH}$ samples can tell which one it sees.
--
--   **Formalization Note** $c$ and $C$ are chosen once, before $\Delta,\eta,n$; $\log$ is the natural logarithm and $L\ge4$, so the real powers are the usual ones. "Finitely supported probability distribution" is a probability measure whose set $\mathrm{Supp}$ of positive-weight atoms is finite and carries all the mass; the mass condition and the separation are the published `IsSeparatedAtomic`. $d_{TV}$ is the published total variation distance `FoundationsRL.DECLower.tvDist`, the supremum over measurable sets of $|P(A)-Q(A)|$, which equals $\tfrac12\int|p-q|$ for probability measures.
--
--   Differences from the source:
--   - encoding: finitely supported probability distribution D on ℝⁿ; D({0}) → IsProbabilityMeasure D, (Supp D).Finite and D((Supp D)ᶜ) = 0 (inside IsSeparatedAtomic Δ D); (D {0}).toReal; reason: a finitely supported distribution is exactly a probability measure carried by a finite set of atoms; the weight of a point is its measure
--   - encoding: dTV(P, Q) = ½∫|p − q| → FoundationsRL.DECLower.tvDist P Q = sup over measurable A of |P(A) − Q(A)| (published definition); reason: the two agree for probability measures (Scheffé); the set form needs no densities
--   - encoding: absolute constants c, C > 0 → ∃ c C : ℝ, 0 < c ∧ 0 < C chosen before Δ, η, n; reason: Lean rendering of absolute constants
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 21, p.29 (PDF p.31); dTV convention p.29; proof pp.30–37

import Mathlib
import Definitions.Def_GaussMixHH_CenterModel
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory

namespace GaussMixHH.Supplement

open GaussMixHH FoundationsRL.DECLower

/-- **Theorem 21** (the moment-matched hard pair).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Theorem 21, p.29 (PDF p.31).

"There are absolute constants c, C > 0 such that the following holds. Let 0 < ∆ ≤ 1, 0 < η ≤ e^{−4},
and let L := log(1/η), H := n^{1/3}L^{4/3}/∆^{4/3}. Suppose n ≥ CL²/∆². Then there are finitely
supported probability distributions D1, D2 on Rn such that: • The distinct centers in each support
are at distance at least ∆ from one another; • D1({0}) = η and D2({0}) = 0. Every nonzero center in
either support has norm at least ∆; • Their homogeneous Gaussian mixtures satisfy
dTV(D1 ∗ ϕn, D2 ∗ ϕn) ≤ e^{−cH}."

**Formalization Note.**
* `c, C` are chosen once, before `∆, η, n`. `log` is `Real.log`; `L ≥ 4 > 0`, so the real powers
  `L^{4/3}` (`Real.rpow`) are the usual ones.
* "Finitely supported probability distribution": `D` is a probability measure, its positive-weight
  atoms `Supp D` form a finite set, and `D((Supp D)ᶜ) = 0`; the last clause and the `∆`-separation of
  distinct atoms are the published `IsSeparatedAtomic ∆ D`. `D({0})` is `(D {0}).toReal`.
* `D ∗ ϕn` is the published `mixture D = D ∗ N(0, I_n)`; `dTV` is the published
  `FoundationsRL.DECLower.tvDist`, the supremum over measurable sets of `|P(A) − Q(A)|`, which equals
  `½∫|p − q|` for probability measures (the paper's convention, p.29, with the factor `½`). -/
theorem theorem_21 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Δ η : ℝ), 0 < Δ → Δ ≤ 1 → 0 < η → η ≤ Real.exp (-4) →
      ∀ n : ℕ, C * Real.log (1 / η) ^ 2 / Δ ^ 2 ≤ (n : ℝ) →
        ∃ (D₁ D₂ : Measure (EuclideanSpace ℝ (Fin n))),
          IsProbabilityMeasure D₁ ∧ IsProbabilityMeasure D₂ ∧
          (Supp D₁).Finite ∧ (Supp D₂).Finite ∧
          IsSeparatedAtomic Δ D₁ ∧ IsSeparatedAtomic Δ D₂ ∧
          (D₁ {0}).toReal = η ∧ D₂ {0} = 0 ∧
          (∀ μ ∈ Supp D₁, μ ≠ 0 → Δ ≤ ‖μ‖) ∧ (∀ μ ∈ Supp D₂, μ ≠ 0 → Δ ≤ ‖μ‖) ∧
          tvDist (mixture D₁) (mixture D₂) ≤
            Real.exp (-(c * ((n : ℝ) ^ ((1 : ℝ) / 3) * Real.log (1 / η) ^ ((4 : ℝ) / 3) /
              Δ ^ ((4 : ℝ) / 3)))) := by sorry

end GaussMixHH.Supplement
