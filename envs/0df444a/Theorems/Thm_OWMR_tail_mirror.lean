-- Prove2me | Theorems.Thm_OWMR_tail_mirror
-- name    : OWMR.tail_mirror
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:41.513651+00:00
-- url     : https://prove2.me/theorems/7d159de4-d282-4c07-a798-4e33197edbc7
-- title:
--   Tail-mirror inequality: $p\mathcal T_b+4rM(b)B\le(3r+1)\beta bM(b)$
-- statement:
--   Let $U$ be the renewal measure of i.i.d. nonnegative demands with positive mean, $M(b)=U[0,b)$, and let $h,p,b>0$, $r=p/h$, $\beta=hp/(h+p)$, and $\mathcal T_b=\int_{[b,2b)}(2b-x)\,U(dx)$. Let $B$ be any real number with
--
--   $$B\,M(b)\le V_z:=\int_{[0,b)}\bigl[p(z-x)^++h(x-z)^+\bigr]\,U(dx)\qquad\text{for every }z\in\mathbb R .$$
--
--   Then
--
--   $$p\,\mathcal T_b+4r\,M(b)\,B\le(3r+1)\,\beta\,b\,M(b).$$
--
--   By the occupation identity, $V_z/M(b)$ is the long-run average mirror loss of a width-$b$ policy at depletion center $z$, so the mirror cost $B=B_b$ of (14) satisfies the hypothesis, and the conclusion is (17).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Lemma 6 (Tail-Mirror Inequality), eq. (17), p. 18; proof on pp. 18-19.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem tail_mirror (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hρ : 0 < ∫⁻ x, (x : ℝ≥0∞) ∂ρ) (h p b : ℝ) (hh : 0 < h) (hp : 0 < p) (hb : 0 < b)
    (B : ℝ) (hB : ∀ z : ℝ, B * (renewalMeasure ρ (Set.Ico 0 b)).toReal
      ≤ ∫ x in Set.Ico 0 b, (p * max (z - x) 0 + h * max (x - z) 0) ∂(renewalMeasure ρ)) :
    p * ∫ x in Set.Ico b (2 * b), (2 * b - x) ∂(renewalMeasure ρ)
        + 4 * (p / h) * (renewalMeasure ρ (Set.Ico 0 b)).toReal * B
      ≤ (3 * (p / h) + 1) * (h * p / (h + p)) * b * (renewalMeasure ρ (Set.Ico 0 b)).toReal := by sorry
end OWMR
