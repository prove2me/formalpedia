-- Prove2me | Theorems.Thm_GradedReserve_Supplement_theorem_6_1
-- name    : GradedReserve.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:55:40.875776+00:00
-- url     : https://prove2.me/theorems/0d5c16f8-4f7f-4790-944c-5174172877fc
-- title:
--   Theorem 6.1 — rounding the continuous equilibrium to a bid grid
-- statement:
--   Let $n\ge2$, $\Delta=1/K$ with $K\in\mathbb N$, $K\ge1$, and let $\tilde\beta=\lceil\beta/\Delta\rceil\Delta$, where types with $\beta(v)\le0$ (exit, or a bid of $0$) exit. Ties go to the lowest index and the exit action is kept.
--
--   1. **Revenue.** For each of the formats $S(\alpha,r)$ ($\alpha\in[0,1]$, $r\in[0,1)$), $\mathrm{LP}(d,\lambda)$ ($d\in(0,1]$, $\lambda\in[0,1]$), $\mathrm{EF}(e,r)$ ($e\ge0$) and the second-price auction with bidder-specific reserves $r_i\in[0,1)$, and for every realized bid vector, the seller's revenue after rounding every bid up to the grid is at least the revenue before rounding. In particular the revenue under $\tilde\beta$ is at least the revenue under $\beta$ at every realization of the values, with no equilibrium property used.
--   2. **Approximate equilibrium.** Let values be i.i.d. with a density positive on $(0,1)$. Let $\beta$ be a symmetric BNE under continuous bids that exits below its participation threshold $a$ and is strictly increasing with valid bids on $(a,1]$, for a format with lowest valid bid $t_0$ on the grid. Then, for almost every type $v$ of bidder $i$ and every grid action $g$, the gain from $g$ over $\tilde\beta(v)$ against opponents playing $\tilde\beta$ is at most
--      1. $(1+\sum_{j\ne i}\kappa_j)\Delta$ for $S(\alpha,r)$, $\mathrm{LP}(d_\lambda,\lambda)$ and $\mathrm{EF}(e,r)$ with $e=(a-r)Q(a)$, when each opponent's valid bids have density at most $\kappa_j$;
--      2. $(1+2(n-1)\bar f/c)\Delta$ for $S(\alpha,r)$ with $0<\alpha\le1$, $0<r<1$ on the grid, $f\le\bar f$ and $\beta'(v)\ge c(v-r)$ ($c>0$) on $(a,1)$;
--      3. $(1+r)\Delta$ for two uniform bidders in the first-price auction $S(1,r)$;
--      4. strictly less than $\Delta$, for truthful bidding in the second-price formats $S(0,r)$ and the second-price auction with bidder-specific reserves on the grid.
--   3. **Lower bound.** For the all-pay auction $\mathrm{LP}(1/4,1)$, two uniform bidders and $1/\Delta\in4\mathbb N$, the rounded equilibrium profile is not a $\delta$-BNE for any $\delta<\Delta$.
--
--   The theorem justifies running the mechanisms of the paper on a discrete bid interface: rounding the continuous equilibrium keeps its revenue in every realization and loses at most an explicit multiple of the grid step.
--
--   Differences from the source:
--   - encoding: 1/Δ ∈ ℕ → Δ = 1/K with K : ℕ, 0 < K; reason: the same grids
--   - encoding: β̃ = ⌈β/Δ⌉Δ; types with β(v) = 0 exit → roundBid Δ: b ≤ 0 ↦ exit (−1), b > 0 ↦ ⌈b/Δ⌉Δ; reason: the same rounded strategies
--   - generalization: part 1: the revenue under β̃ is at least the revenue under β at the same values, for β the format's equilibrium (truthful in the second-price formats) → for every bid vector x with entries ≤ 1 and every mechanism of the four families (any parameters in range), realizedRevenue M x ≤ realizedRevenue M (roundBid Δ ∘ x); reason: taking x = β(V) at a realization of the values gives the paper's claim; the proof uses no equilibrium property for any format
--   - encoding: n bidders, values from F (Section 2) → 2 ≤ n; IsValueDensity f in parts 2(i), 2(ii), 2(iv); powerDensity 1 for uniform; reason: Section 2 standing assumptions
--   - encoding: mixed strategies with an exit action, independent private randomizations → one Markov kernel per bidder from values to actions in ℝ; negative actions (and actions above 1) are exit; the action profile law is the product of the bidders' action laws; reason: Lean convention; the same strategies
--   - reading: a Bayes–Nash equilibrium → IsBNE: for every bidder, almost every type (for the value law) best-responds; reason: the paper's convention, "Statements about types are understood up to F-null sets" (p.26)
--   - reading: the symmetric strictly increasing BNE under continuous bids → a measurable β with IsBNE of the constant profile and IsMonoBidShape β a t₀: exit below a, valid bids in [t₀,1] and strictly increasing on (a,1]; reason: the shape the proof uses (participation threshold a, lowest valid bid t₀, p.33)
--   - generalization: strictly increasing β (including the type a) → the action of the single type a is unconstrained; reason: one type has probability zero; it does not affect the opponents' laws or the a.e. conclusion
--   - reading: play a δ-BNE, type by type, with δ ≤ … → for almost every type v and every grid action g (grid point or exit), gridGain ≤ the bound; reason: BNE are up to null sets of types in this paper
--   - encoding: each opponent's valid bids have density at most κⱼ → P(β(Vⱼ) ∈ (x,y]) ≤ κⱼ (y − x) for t₀ ≤ x ≤ y ≤ 1, j ≠ i; reason: equivalent to a density bound on [t₀,1]
--   - encoding: reserves and minimum bids on the grid → IsGridPoint Δ t₀ (r, d_λ, or the entry threshold r); IsGridPoint Δ rᵢ for bidder-specific reserves; reason: the stated placement
--   - reading: β′(v) ≥ c(v − r) → β has a derivative D ≥ c(v − r) at every v ∈ (a,1), c > 0; reason: on the participation region, where the proof uses it
--   - reading: f ≤ f̄ → f v ≤ f̄ for v ∈ [0,1]; reason: the density on the support
--   - reading: δ < Δ for the second-price formats → for a.e. type and every grid action, gridGain < Δ (type by type), for S(0,r) and the auction with bidder-specific reserves (rᵢ = 0 without reserves), with truthful β; reason: the proof bounds each type's loss below Δ in every realization; a uniform δ < Δ fails at Δ = 1 (n = 2, uniform values, rᵢ = 0: the lower-index bidder's gain is 1 − v, whose supremum over types is Δ)
--   - reading: δ ≥ Δ for the all-pay auction with d = 1/4 → for every δ < Δ the rounded profile of any symmetric strictly increasing BNE β (threshold a, t₀ = 1/4) is not a δ-BNE: not every bidder has gridGain ≤ δ for a.e. type; reason: the stated lower bound, in the same type-by-type sense
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 6.1, p.11 (PDF 12); proof pp.33–35 (PDF 34–36)

import Mathlib
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_Supplement_Mechanism
import Definitions.Def_GradedReserve_Supplement_realizedRevenue
import Definitions.Def_GradedReserve_Supplement_stdMech
import Definitions.Def_GradedReserve_Supplement_lpMech
import Definitions.Def_GradedReserve_Supplement_efMech
import Definitions.Def_GradedReserve_Supplement_spReserveMech
import Definitions.Def_GradedReserve_Supplement_IsBNE
import Definitions.Def_GradedReserve_Supplement_roundBid
import Definitions.Def_GradedReserve_Supplement_IsGridPoint
import Definitions.Def_GradedReserve_Supplement_gridGain
import Definitions.Def_GradedReserve_Supplement_IsMonoBidShape
import Definitions.Def_GradedReserve_Supplement_IsRoundingFormat
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- **Theorem 6.1** (Rounding to a bid grid) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 6.1, p.11, PDF 12; proof pp.33–35,
PDF 34–36). Restrict bids to the grid `{0, Δ, …, 1}` with `1/Δ ∈ ℕ`, break ties in favor of the
lowest index, place reserves and minimum bids on the grid, and keep the exit action. Let `β` be
the symmetric strictly increasing BNE under continuous bids of `S(α, r)`, of `LP(d_λ, λ)`, of
`EF(e, r)` with `e = (a − r)Q(a)`, or truthful bidding in the second-price auction with or without
bidder-specific reserves applied before ranking, and let `β̃ = ⌈β/Δ⌉Δ`.
1. In every realization the seller's revenue under `β̃` is at least the revenue under `β` at the
   same values; for the first three formats this needs no equilibrium property.
2. Types with `β(v) = 0` exit, and the others play a `δ`-BNE, type by type, with
   `δ ≤ (1 + Σ_{j≠i} κⱼ)Δ` for `S(α, r)`, `LP` and `EF` when each opponent's valid bids have
   density at most `κⱼ`; `δ ≤ (1 + 2(n − 1)f̄/c)Δ` for `S(α, r)` with `0 < α ≤ 1`, `0 < r < 1`,
   `f ≤ f̄` and `β′(v) ≥ c(v − r)`; `δ ≤ (1 + r)Δ` for two uniform bidders in the first-price
   auction; and `δ < Δ` for the second-price formats.
3. For the all-pay auction with `d = 1/4`, two uniform bidders and `1/Δ ∈ 4ℕ`, `δ ≥ Δ`.

**Formalization Note.** `Δ = 1/K` with `K ∈ ℕ`, `K ≥ 1`. `β̃ = roundBid Δ ∘ β` (exit, and a bid
of `0`, become exit). Part 1 is stated for every realized bid vector (bids at most `1`, negative
entries exit) and every mechanism of the four families, which covers `β` and `β̃` at every
realization of values. In part 2, "the symmetric strictly increasing BNE" is a measurable `β`
that is a symmetric BNE (`IsBNE`, best responses for almost every type) of shape
`IsMonoBidShape β a t₀` (exit below the participation threshold `a`, valid and strictly increasing
on `(a, 1]`), where `t₀` is the format's lowest valid bid, placed on the grid; "`δ`-BNE type by
type" is a bound on `gridGain` for almost every type and every grid action (grid points and exit);
"density at most `κⱼ`" is `P(β(Vⱼ) ∈ (x, y]) ≤ κⱼ (y − x)` for `t₀ ≤ x ≤ y ≤ 1`; "`β′(v) ≥ c(v − r)`"
holds at every type of `(a, 1)`, with `c > 0`; "`δ < Δ`" is read type by type (each type's gain is
below `Δ`); the second-price formats are `S(0, r)` and the auction with bidder-specific reserves
`rᵢ ∈ [0, 1)` (`rᵢ = 0` without reserves), with truthful `β(v) = v`. Part 3 says the rounded
profile is not a `δ`-BNE for any `δ < Δ`. -/
theorem theorem_6_1 (n : ℕ) (hn : 2 ≤ n) (K : ℕ) (hK : 0 < K) (Δ : ℝ) (hΔ : Δ = 1 / (K : ℝ)) :
    (∀ M : Mechanism n,
      ((∃ α r : ℝ, α ∈ Icc (0:ℝ) 1 ∧ r ∈ Ico (0:ℝ) 1 ∧ M = stdMech n α r) ∨
        (∃ d lam : ℝ, d ∈ Ioc (0:ℝ) 1 ∧ lam ∈ Icc (0:ℝ) 1 ∧ M = lpMech n d lam) ∨
        (∃ e r : ℝ, 0 ≤ e ∧ M = efMech n e r) ∨
        (∃ rr : Fin n → ℝ, (∀ j, rr j ∈ Ico (0:ℝ) 1) ∧ M = spReserveMech n rr)) →
      ∀ x : Fin n → ℝ, (∀ j, x j ≤ 1) →
        realizedRevenue M x ≤ realizedRevenue M (fun j => roundBid Δ (x j))) ∧
    (∀ f : ℝ → ℝ, IsValueDensity f → ∀ (M : Mechanism n) (a t₀ : ℝ),
      IsRoundingFormat n f a M t₀ → IsGridPoint Δ t₀ →
      ∀ (β : ℝ → ℝ) (hβ : Measurable β), IsBNE M f (fun _ => Kernel.deterministic β hβ) →
      IsMonoBidShape β a t₀ →
      ∀ (i : Fin n) (κ : Fin n → ℝ),
        (∀ j, j ≠ i → ∀ x y : ℝ, t₀ ≤ x → x ≤ y → y ≤ 1 →
          ((typeMeasure f).map β (Ioc x y)).toReal ≤ κ j * (y - x)) →
        ∀ᵐ v ∂(typeMeasure f), ∀ g : ℝ, (g < 0 ∨ IsGridPoint Δ g) →
          gridGain M f (fun w => roundBid Δ (β w)) i v g
            ≤ (1 + ∑ j ∈ Finset.univ.erase i, κ j) * Δ) ∧
    (∀ f : ℝ → ℝ, IsValueDensity f → ∀ α r : ℝ, 0 < α → α ≤ 1 → 0 < r → r < 1 →
      IsGridPoint Δ r → ∀ fbar c : ℝ, (∀ v ∈ Icc (0:ℝ) 1, f v ≤ fbar) → 0 < c →
      ∀ (a : ℝ) (β : ℝ → ℝ) (hβ : Measurable β),
        IsBNE (stdMech n α r) f (fun _ => Kernel.deterministic β hβ) → IsMonoBidShape β a r →
        (∀ v ∈ Ioo a 1, ∃ D : ℝ, HasDerivAt β D v ∧ c * (v - r) ≤ D) →
        ∀ i : Fin n, ∀ᵐ v ∂(typeMeasure f), ∀ g : ℝ, (g < 0 ∨ IsGridPoint Δ g) →
          gridGain (stdMech n α r) f (fun w => roundBid Δ (β w)) i v g
            ≤ (1 + 2 * ((n : ℝ) - 1) * fbar / c) * Δ) ∧
    (∀ r ∈ Ico (0:ℝ) 1, IsGridPoint Δ r → ∀ (a : ℝ) (β : ℝ → ℝ) (hβ : Measurable β),
      IsBNE (stdMech 2 1 r) (powerDensity 1) (fun _ => Kernel.deterministic β hβ) →
      IsMonoBidShape β a r →
      ∀ i : Fin 2, ∀ᵐ v ∂(typeMeasure (powerDensity 1)), ∀ g : ℝ, (g < 0 ∨ IsGridPoint Δ g) →
        gridGain (stdMech 2 1 r) (powerDensity 1) (fun w => roundBid Δ (β w)) i v g
          ≤ (1 + r) * Δ) ∧
    (∀ f : ℝ → ℝ, IsValueDensity f →
      (∀ rr : Fin n → ℝ, (∀ j, rr j ∈ Ico (0:ℝ) 1 ∧ IsGridPoint Δ (rr j)) →
        ∀ i : Fin n, ∀ᵐ v ∂(typeMeasure f), ∀ g : ℝ, (g < 0 ∨ IsGridPoint Δ g) →
          gridGain (spReserveMech n rr) f (fun w => roundBid Δ w) i v g < Δ) ∧
      (∀ r ∈ Ico (0:ℝ) 1, IsGridPoint Δ r →
        ∀ i : Fin n, ∀ᵐ v ∂(typeMeasure f), ∀ g : ℝ, (g < 0 ∨ IsGridPoint Δ g) →
          gridGain (stdMech n 0 r) f (fun w => roundBid Δ w) i v g < Δ)) ∧
    (4 ∣ K → ∀ (a : ℝ) (β : ℝ → ℝ) (hβ : Measurable β),
      IsBNE (lpMech 2 (1 / 4) 1) (powerDensity 1) (fun _ => Kernel.deterministic β hβ) →
      IsMonoBidShape β a (1 / 4) →
      ∀ δ < Δ, ¬ ∀ i : Fin 2, ∀ᵐ v ∂(typeMeasure (powerDensity 1)), ∀ g : ℝ,
        (g < 0 ∨ IsGridPoint Δ g) →
          gridGain (lpMech 2 (1 / 4) 1) (powerDensity 1) (fun w => roundBid Δ (β w)) i v g
            ≤ δ) := by sorry

end GradedReserve.Supplement
