-- Prove2me | Theorems.Thm_GradedReserve_Supplement_theorem_4_2
-- name    : GradedReserve.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:53:29.954263+00:00
-- url     : https://prove2.me/theorems/8eb7e10e-2347-4f78-9dac-74fb5faf05da
-- title:
--   Theorem 4.2 — payments and user utility under $\mathrm{LP}(d,\lambda)$ against arbitrary opponents
-- statement:
--   Let all values and actions $(V_j,X_j)_{j\le n}$ live on one probability space, with any joint distribution and no assumption on the opponents; actions are at most $1$ (bids in $[0,1]$, negative actions exit). Fix a bidder $i$ with integrable value $V_i$, $d\in(0,1]$ and $\lambda\in[0,1]$. Let $p_i$ be $i$'s payment under $\mathrm{LP}(d,\lambda)$ at the realized bids and $u_i=\mathbb E\big[V_i\mathbf 1\{i\text{ wins}\}-p_i\big]$ the expected utility of the user that $i$ represents. Then:
--
--   1. the seller receives at least $\lambda\,\mathbb E[X_i;X_i\ge d]$ from $i$ in expectation, and under $\mathrm{EF}(e,r)$ (any $r$, any $e\ge0$) at least $e\,\mathbb P(X_i\ge r,\ X_i>0)$;
--   2. $$u_i=\mathbb E\big[(V_i-X_i)\mathbf 1\{i\text{ wins}\}\big]-\lambda\,\mathbb E\big[X_i;\ X_i\ge d,\ i\text{ loses}\big];$$
--   3. if $X_i\ge V_i-\eta$ almost surely on $\{X_i\ge d\}$, then
--   $$u_i\le\eta\,\mathbb P(i\text{ wins})-\lambda\,\mathbb E\big[X_i;\ X_i\ge d,\ i\text{ loses}\big],$$
--   and an anchored bidder ($X_i=V_i$ a.s.) has $u_i<0$ whenever $\lambda>0$ and $\mathbb P(X_i\ge d,\ i\text{ loses})>0$.
--
--   The bounds hold whatever the opponents do: loser payments extract revenue from, and impose negative utility on, bidders who do not shade.
--
--   Differences from the source:
--   - generalization: the value Vᵢ of bidder i (values in [0,1], Section 2) → any integrable real random variable Vᵢ; reason: the proof uses only integrability; values in [0,1] are integrable
--   - encoding: any joint distribution of the values and bids → one probability space carrying measurable V_j, X_j for all bidders, with arbitrary dependence; bids X_j ≤ 1, negative X_j is exit; reason: the same objects; bids lie in [0,1] (Section 2)
--   - encoding: i wins / i loses → (lpMech n d λ).alloc at the realized bid vector equals 1 / equals 0 (lowest-index ties); reason: Definition 4.1
--   - reading: Xᵢ ≥ Vᵢ − η on {Xᵢ ≥ d} → almost surely on {Xᵢ ≥ d}; reason: an almost-sure hypothesis covers the pointwise one
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.2, p.9 (PDF 10); proof p.32 (PDF 33)

import Mathlib
import Definitions.Def_GradedReserve_Supplement_lpMech
import Definitions.Def_GradedReserve_Supplement_efMech
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- **Theorem 4.2** (Payments and user utility against arbitrary opponents) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.2,
p.9, PDF 10; proof p.32, PDF 33). Let bidder `i`'s value and bid `(Vᵢ, Xᵢ)` have any joint
distribution, with no assumption on the opponents, and let `uᵢ = E[Vᵢ 1{i wins} − pᵢ]` be the
expected utility of the user that `i` represents, where `pᵢ` is `i`'s payment. Under `LP(d, λ)`:
1. the seller receives at least `λ E[Xᵢ; Xᵢ ≥ d]` from `i` in expectation, and at least
   `e P(Xᵢ ≥ r, Xᵢ > 0)` under `EF(e, r)`;
2. `uᵢ = E[(Vᵢ − Xᵢ)1{i wins}] − λ E[Xᵢ; Xᵢ ≥ d, i loses]`;
3. if `Xᵢ ≥ Vᵢ − η` on `{Xᵢ ≥ d}`, then `uᵢ ≤ η P(i wins) − λ E[Xᵢ; Xᵢ ≥ d, i loses]`, so an
   anchored bidder (`Xᵢ = Vᵢ`) has `uᵢ < 0` whenever `λ > 0` and it loses with a valid bid with
   positive probability.

**Formalization Note.** All `n` values and actions live on one probability space with an arbitrary
joint law. Actions are at most `1` (bids lie in `[0, 1]`; negative actions are exit). "i wins" is
`(lpMech n d λ).alloc = 1` at the realized profile (lowest-index ties). Values may be any
integrable real random variable. "On `{Xᵢ ≥ d}`" is read almost surely. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (V X : Fin n → Ω → ℝ) (hV : ∀ j, Measurable (V j)) (hX : ∀ j, Measurable (X j))
    (hX1 : ∀ j ω, X j ω ≤ 1) (i : Fin n) (hVi : Integrable (V i) P)
    (d lam : ℝ) (hd : d ∈ Ioc (0:ℝ) 1) (hlam : lam ∈ Icc (0:ℝ) 1) :
    (lam * ∫ ω, (if d ≤ X i ω then X i ω else 0) ∂P ≤
        ∫ ω, (lpMech n d lam).pay (fun j => X j ω) i ∂P) ∧
    (∀ e r : ℝ, 0 ≤ e →
      e * (P {ω | r ≤ X i ω ∧ 0 < X i ω}).toReal ≤
        ∫ ω, (efMech n e r).pay (fun j => X j ω) i ∂P) ∧
    (∫ ω, (V i ω * (lpMech n d lam).alloc (fun j => X j ω) i
          - (lpMech n d lam).pay (fun j => X j ω) i) ∂P =
      ∫ ω, (V i ω - X i ω) * (lpMech n d lam).alloc (fun j => X j ω) i ∂P
        - lam * ∫ ω, (if d ≤ X i ω ∧ (lpMech n d lam).alloc (fun j => X j ω) i = 0
            then X i ω else 0) ∂P) ∧
    (∀ η : ℝ, (∀ᵐ ω ∂P, d ≤ X i ω → V i ω - η ≤ X i ω) →
      ∫ ω, (V i ω * (lpMech n d lam).alloc (fun j => X j ω) i
          - (lpMech n d lam).pay (fun j => X j ω) i) ∂P ≤
        η * (P {ω | (lpMech n d lam).alloc (fun j => X j ω) i = 1}).toReal
          - lam * ∫ ω, (if d ≤ X i ω ∧ (lpMech n d lam).alloc (fun j => X j ω) i = 0
              then X i ω else 0) ∂P) ∧
    ((∀ᵐ ω ∂P, X i ω = V i ω) → 0 < lam →
      0 < P {ω | d ≤ X i ω ∧ (lpMech n d lam).alloc (fun j => X j ω) i = 0} →
      ∫ ω, (V i ω * (lpMech n d lam).alloc (fun j => X j ω) i
          - (lpMech n d lam).pay (fun j => X j ω) i) ∂P < 0) := by sorry

end GradedReserve.Supplement
