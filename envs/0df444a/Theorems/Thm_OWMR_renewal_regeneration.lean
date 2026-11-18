-- Prove2me | Theorems.Thm_OWMR_renewal_regeneration
-- name    : OWMR.renewal_regeneration
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T03:06:33.051461+00:00
-- url     : https://prove2.me/theorems/ed4417a1-41e4-4330-8c2d-c3a9f9766d91
-- title:
--   Regeneration at first passage: $\int_{[c,\infty)}f\,dU\le\sup_{y\ge c}\int f(y+x)\,U(dx)$
-- statement:
--   Let $D_1,D_2,\ldots$ be i.i.d. nonnegative demands with law $\rho$ (point masses, including a mass at $0$, are allowed), $D^{(n)}=D_1+\cdots+D_n$, and let $U(A)=\sum_{n\ge0}\mathbb P(D^{(n)}\in A)$ be the renewal measure. For every level $c\in\mathbb R$ and every measurable $f:\mathbb R\to[0,\infty]$,
--
--   $$\int_{[c,\infty)}f\,dU\;\le\;\sup_{y\ge c}\int f(y+x)\,U(dx).$$
--
--   This is the regeneration (strong Markov) property of the partial sums at the first passage $\tau_c=\inf\{n\ge0:D^{(n)}\ge c\}$, in the form used by the source: the partial sums at or above $c$ are $Y+D'^{(m)}$, $m\ge0$, where $Y=D^{(\tau_c)}\ge c$ is the first-passage position and $D'$ is a fresh copy of the partial-sum process independent of $Y$; since the first-passage law has total mass at most $1$, the weighted count of partial sums in $[c,\infty)$ is at most the worst case over starting positions $y\ge c$. The inequality needs no moment assumption and no almost-sure finiteness of $\tau_c$.
--
--   It is the step used in the proof of Lemma 2 (interval counts after the first passage of $x$) and of Lemma 5 (the split of a full cycle at the first passage of the half width $b$).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.2, Step 1 of the proof of Lemma 2 (first passage tau_x and fresh demands), p. 13, and Step 1 of the proof of Lemma 5 (split at tau_b, Y = D^(tau_b)), pp. 16-17.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem renewal_regeneration (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (c : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x in Set.Ici c, f x ∂(renewalMeasure ρ)
      ≤ ⨆ y ∈ Set.Ici c, ∫⁻ x, f (y + x) ∂(renewalMeasure ρ) := by sorry
end OWMR
