-- Prove2me | Theorems.Thm_GradedReserve_Supplement_theorem_4_3
-- name    : GradedReserve.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:54:41.561804+00:00
-- url     : https://prove2.me/theorems/aed86ffe-86ba-4f0b-a82c-aa8b793bba00
-- title:
--   Theorem 4.3 — a revenue-neutral loser-payment family $\mathrm{LP}(d_\lambda,\lambda)$
-- statement:
--   Let $n\ge2$ and values i.i.d. on $[0,1]$ with a density $f$ positive on $(0,1)$ (Section 2). Write $Q=F^{n-1}$, $T_\lambda(v)=\lambda+(1-\lambda)Q(v)$ and $m_a(v)=vQ(v)-\int_a^vQ$; fix $a\in(0,1)$ and set $d_\lambda=aQ(a)/T_\lambda(a)$.
--
--   1. For every $\lambda\in[0,1]$, $\beta_\lambda(v)=m_a(v)/T_\lambda(v)$ for $v\ge a$, with exit below $a$, is a symmetric BNE of $\mathrm{LP}(d_\lambda,\lambda)$ with revenue $R_n(a)$, and every BNE of $\mathrm{LP}(d_\lambda,\lambda)$ has revenue $R_n(a)$. For uniform values
--   $$d_\lambda=\frac{a^n}{\lambda+(1-\lambda)a^{n-1}},\qquad \beta_\lambda(v)=\frac{(n-1)v^n+a^n}{n[\lambda+(1-\lambda)v^{n-1}]}\quad(v\ge a).$$
--   2. $d_\lambda$ is strictly decreasing in $\lambda\in[0,1]$.
--   3. For every law of the bid vector $X$ that does not depend on $\lambda$ (no independence across bidders required), $\lambda\mapsto\mathbb E[\mathrm{Rev}_\lambda(X)]$ under $\mathrm{LP}(d_\lambda,\lambda)$ is non-decreasing on $[0,1]$.
--   4. For two uniform anchored bidders and $a=\tfrac12$, $d=d_\lambda=\frac1{2(1+\lambda)}$, and the revenue per round and the utility per user and round are
--   $$\mathrm{Rev}_{\mathrm{anc}}(\lambda)=\tfrac23(1-d^3)+\lambda\Big[(1-d^2)-\tfrac23(1-d^3)\Big],\qquad u(\lambda)=-\frac\lambda2\Big[(1-d^2)-\tfrac23(1-d^3)\Big];$$
--   $\mathrm{Rev}_{\mathrm{anc}}$ is non-decreasing and $u$ non-increasing in $\lambda$, with $\mathrm{Rev}_{\mathrm{anc}}(1)=15/16$ and $u(1)=-9/64$.
--   5. In $\mathrm{LP}(d,1)$, $d\in(0,1]$: if a bidder faces opponents whose actions have any fixed joint law and wins with bid $b$ with probability $W(b)\le b$ for all $b\in[d,1]$, then for every value $v\in[0,1]$ no action has positive expected utility (exit is a best response), and for $v<1$ every valid bid has negative expected utility. In particular, if one opponent bids its value, uniform on $[0,1]$, every rational bidder with uniform values exits almost surely: its valid bids have probability zero, for every $n$.
--
--   Rational bidders neutralize the loser payment by shading and by the lower minimum bid, so rational revenue does not depend on $\lambda$, while bidders who do not adapt pay more as $\lambda$ grows.
--
--   **Formalization Note** Uniform values are `powerDensity 1`; anchored bidders form the truthful profile.
--
--   Differences from the source:
--   - encoding: the standing assumptions on F → IsValueDensity f and 2 ≤ n (Section 2); reason: Section 2's assumptions; Section 3's regularity is not used (p.32)
--   - encoding: mixed strategies with an exit action, independent private randomizations → one Markov kernel per bidder from values to actions in ℝ; negative actions (and actions above 1) are exit; the action profile law is the product of the bidders' action laws; reason: Lean convention; the same strategies
--   - reading: a Bayes–Nash equilibrium → IsBNE: for every bidder, almost every type (for the value law) best-responds; reason: the paper's convention, "Statements about types are understood up to F-null sets" (p.26)
--   - encoding: exit below a → lpBid = −1 for v < a; reason: negative actions are exit
--   - encoding: β_λ is a symmetric BNE → ∃ hβ : Measurable β_λ, IsBNE of the constant deterministic profile; reason: measurability of β_λ is part of the conclusion
--   - encoding: E[Rev_λ(X)] for a bid vector with any joint distribution → ∫ realizedRevenue (lpMech (d_λ) λ) x dμ for any probability measure μ on Fin n → ℝ; reason: realizedRevenue is display (8)
--   - reading: both monotone in λ → Rev_anc non-decreasing (MonotoneOn) and u non-increasing (AntitoneOn) on [0,1]; reason: the directions the proof establishes (p.33)
--   - encoding: two uniform anchored bidders; utility per user → n = 2, powerDensity 1, the truthful profile; expRevenue and expUtility of each bidder; reason: the same quantities
--   - reading: faces mechanism-invariant opponents … wins with bid b with probability W(b) ≤ b for all b ≥ d → an arbitrary law μ of the opponents' actions; W = allocAgainst (lpMech d 1) μ i, assumed ≤ b for b ∈ [d,1]; reason: mechanism-invariant opponents have a fixed law of bids; bids above 1 are not in the action space
--   - reading: exit is a best response, strictly for values below one → ∀ v ∈ [0,1], every action has payoff ≤ 0 (exit's payoff); for v < 1 every valid bid b ∈ [d,1] has payoff < 0; reason: invalid bids are payoff-equivalent to exit
--   - reading: every rational bidder exits almost surely → a bidder with uniform values whose kernel best-responds for a.e. type puts zero probability on valid bids [d,1]; reason: invalid bids are exit-equivalent (Section B normalization); values equal to 1 have probability zero
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 4.3, pp.9–10 (PDF 10–11); proof pp.32–33 (PDF 33–34)

import Mathlib
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_bidLaw
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_Supplement_lpMech
import Definitions.Def_GradedReserve_Supplement_lpT
import Definitions.Def_GradedReserve_Supplement_lpM
import Definitions.Def_GradedReserve_Supplement_lpMinBid
import Definitions.Def_GradedReserve_Supplement_lpBid
import Definitions.Def_GradedReserve_Supplement_IsBNE
import Definitions.Def_GradedReserve_Supplement_expRevenue
import Definitions.Def_GradedReserve_Supplement_expUtility
import Definitions.Def_GradedReserve_Supplement_realizedRevenue
import Definitions.Def_GradedReserve_Supplement_payoffAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- **Theorem 4.3** (A revenue-neutral loser-payment family) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 4.3, pp.9–10,
PDF 10–11; proof pp.32–33, PDF 33–34). Under the standing assumptions on `F` (Section 2: values
i.i.d. on `[0, 1]` with a density positive on `(0, 1)`, `n ≥ 2`), let `T_λ(v) = λ + (1 − λ)Q(v)`
and `m_a(v) = vQ(v) − ∫_a^v Q`. Fix `a ∈ (0, 1)` and set `d_λ = aQ(a)/T_λ(a)`.
1. `β_λ(v) = m_a(v)/T_λ(v)` for `v ≥ a`, with exit below `a`, is a symmetric BNE of `LP(d_λ, λ)`
   with revenue `R_n(a)` for every `λ ∈ [0, 1]`; every BNE has this revenue. For uniform values
   `d_λ = aⁿ/(λ + (1 − λ)aⁿ⁻¹)` and `β_λ(v) = ((n − 1)vⁿ + aⁿ)/(n[λ + (1 − λ)vⁿ⁻¹])`.
2. `d_λ` is strictly decreasing in `λ`.
3. If the joint distribution of the bid vector does not depend on `λ`, then `E[Rev_λ(X)]` under
   `LP(d_λ, λ)` is non-decreasing in `λ`; independence across bidders is not required.
4. For two uniform anchored bidders and `a = 1/2`, with `d = d_λ = 1/(2(1 + λ))`, the revenue per
   round and the utility per user and round are
   `Rev_anc(λ) = (2/3)(1 − d³) + λ[(1 − d²) − (2/3)(1 − d³)]`,
   `u(λ) = −(λ/2)[(1 − d²) − (2/3)(1 − d³)]`, both monotone in `λ` (revenue non-decreasing,
   utility non-increasing), with `Rev_anc(1) = 15/16` and `u(1) = −9/64`.
5. If a rational bidder faces mechanism-invariant opponents in `LP(d, 1)` and wins with bid `b`
   with probability `W(b) ≤ b` for all `b ≥ d`, then exit is a best response, strictly for values
   below one; in particular, if one opponent is anchored with uniform values, every rational
   bidder exits almost surely, for every `n`.

**Formalization Note.** The binder `lam` is the paper's `λ`. Uniform values are
`powerDensity 1`. Part 3: the bid vector has an arbitrary law `μ` on `Fin n → ℝ`, and
`realizedRevenue` is display (8). Part 4: anchored bidders are the truthful profile
`σ v = δ_v`. Part 5: the opponents' action profile has an arbitrary law `μ` (any dependence); the
rational bidder's payoffs are `payoffAgainst`; "exit is a best response" means no action has
positive payoff (exit has payoff `0`), "strictly" that every valid bid has negative payoff; the
"in particular" clause takes a rational bidder with uniform values that best-responds for almost
every type, and "exits almost surely" means its valid bids have probability zero (invalid bids
are payoff-equivalent to exit). -/
theorem theorem_4_3 (n : ℕ) (hn : 2 ≤ n) :
    (∀ f : ℝ → ℝ, IsValueDensity f → ∀ a ∈ Ioo (0:ℝ) 1,
      (∀ lam ∈ Icc (0:ℝ) 1, ∃ hβ : Measurable (lpBid f n a lam),
        IsBNE (lpMech n (lpMinBid f n a lam) lam) f
          (fun _ => Kernel.deterministic (lpBid f n a lam) hβ) ∧
        expRevenue (lpMech n (lpMinBid f n a lam) lam) f
          (fun _ => Kernel.deterministic (lpBid f n a lam) hβ) = revCurve f n a ∧
        ∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (lpMech n (lpMinBid f n a lam) lam) f σ →
          expRevenue (lpMech n (lpMinBid f n a lam) lam) f σ = revCurve f n a) ∧
      StrictAntiOn (lpMinBid f n a) (Icc 0 1) ∧
      ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ →
        MonotoneOn (fun lam => ∫ x, realizedRevenue (lpMech n (lpMinBid f n a lam) lam) x ∂μ)
          (Icc 0 1)) ∧
    (∀ a ∈ Ioo (0:ℝ) 1, ∀ lam ∈ Icc (0:ℝ) 1,
      lpMinBid (powerDensity 1) n a lam = a ^ n / (lam + (1 - lam) * a ^ (n - 1)) ∧
      ∀ v ∈ Icc a 1, lpBid (powerDensity 1) n a lam v =
        ((n - 1 : ℝ) * v ^ n + a ^ n) / (n * (lam + (1 - lam) * v ^ (n - 1)))) ∧
    (∀ lam ∈ Icc (0:ℝ) 1, lpMinBid (powerDensity 1) 2 (1 / 2) lam = 1 / (2 * (1 + lam))) ∧
    (∀ lam ∈ Icc (0:ℝ) 1,
      expRevenue (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) lam) lam) (powerDensity 1)
          (fun _ => Kernel.deterministic id measurable_id) =
        2 / 3 * (1 - lpMinBid (powerDensity 1) 2 (1 / 2) lam ^ 3)
          + lam * ((1 - lpMinBid (powerDensity 1) 2 (1 / 2) lam ^ 2)
            - 2 / 3 * (1 - lpMinBid (powerDensity 1) 2 (1 / 2) lam ^ 3))) ∧
    (∀ lam ∈ Icc (0:ℝ) 1, ∀ i : Fin 2,
      expUtility (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) lam) lam) (powerDensity 1)
          (fun _ => Kernel.deterministic id measurable_id) i =
        -(lam / 2) * ((1 - lpMinBid (powerDensity 1) 2 (1 / 2) lam ^ 2)
            - 2 / 3 * (1 - lpMinBid (powerDensity 1) 2 (1 / 2) lam ^ 3))) ∧
    MonotoneOn (fun lam => expRevenue (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) lam) lam)
        (powerDensity 1) (fun _ => Kernel.deterministic id measurable_id)) (Icc 0 1) ∧
    (∀ i : Fin 2, AntitoneOn (fun lam => expUtility
        (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) lam) lam) (powerDensity 1)
        (fun _ => Kernel.deterministic id measurable_id) i) (Icc 0 1)) ∧
    expRevenue (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) 1) 1) (powerDensity 1)
        (fun _ => Kernel.deterministic id measurable_id) = 15 / 16 ∧
    (∀ i : Fin 2, expUtility (lpMech 2 (lpMinBid (powerDensity 1) 2 (1 / 2) 1) 1)
        (powerDensity 1) (fun _ => Kernel.deterministic id measurable_id) i = -9 / 64) ∧
    (∀ d ∈ Ioc (0:ℝ) 1, ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ → ∀ i : Fin n,
      (∀ b ∈ Icc d 1, allocAgainst (lpMech n d 1) μ i b ≤ b) →
      ∀ v ∈ Icc (0:ℝ) 1,
        (∀ b : ℝ, payoffAgainst (lpMech n d 1) μ i v b ≤ 0) ∧
        (v < 1 → ∀ b ∈ Icc d 1, payoffAgainst (lpMech n d 1) μ i v b < 0)) ∧
    (∀ d ∈ Ioc (0:ℝ) 1, ∀ μ : Measure (Fin n → ℝ), IsProbabilityMeasure μ → ∀ i j : Fin n,
      i ≠ j → μ.map (fun x => x j) = volume.restrict (Icc (0:ℝ) 1) →
      ∀ σi : Kernel ℝ ℝ, (∀ v ∈ Icc (0:ℝ) 1, IsProbabilityMeasure (σi v) ∧ σi v (Ioi 1) = 0) →
      (∀ᵐ v ∂(typeMeasure (powerDensity 1)), ∀ b : ℝ,
        payoffAgainst (lpMech n d 1) μ i v b ≤ ∫ b', payoffAgainst (lpMech n d 1) μ i v b' ∂(σi v)) →
      bidLaw (powerDensity 1) σi (Icc d 1) = 0) := by sorry

end GradedReserve.Supplement
