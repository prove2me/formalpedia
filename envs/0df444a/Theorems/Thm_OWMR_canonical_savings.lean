-- Prove2me | Theorems.Thm_OWMR_canonical_savings
-- name    : OWMR.canonical_savings
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:32.731209+00:00
-- url     : https://prove2.me/theorems/2419303a-5087-4c99-9dd3-e64d174de3aa
-- title:
--   Lemma 3 (canonical savings and width): g(x)=G-F(Ŝ-x) is continuous, concave, in [0,G], vanishes at ŵ and integrates to k; G>0, and βŵ≤G when H≥h
-- statement:
--   Fix a retailer $i$ of a network under the standing assumptions of Section 3, with lead-time-demand cost $F=F_i$ from (8), holding rate $H=H_i$, and renewal measure $U$ of its one-period demand (9). Let $k>0$ be a planning setup cost and $(\hat s,\hat S)$ a canonical optimum of Lemma 1 at setup cost $k$ (`IsCanonicalOptimum`), with canonical width $\hat w=\hat S-\hat s$, planning value $G=J(k)=\mathcal J_D(F;k)$, savings $g(x)=G-F(\hat S-x)$ and $\beta=hp/(h+p)$. Then:
--   - $g$ is continuous and concave (on all of $\mathbb R$);
--   - $0\le g\le G$ on $[0,\hat w]$ and $g(\hat w)=0$;
--   - $g$ is integrable on $[0,\hat w)$ against $U$, and $\int_{[0,\hat w)}g\,dU=k$;
--   - $g(x)\le p(\hat w-x)$ for $0\le x\le\hat w$;
--   - $G>0$, and if $H\ge h$ then $\beta\hat w\le G$.
--
--   In the Lean statement $G$ is the real number with $J_i(k)=G$ (as an extended nonnegative real); $G>0$ determines it uniquely.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.3, Lemma 3 (Canonical Savings and Width) with the savings and the rate beta of (11), the canonical average-cost identity (13) and the renewal measure (9), pp. 13 and 15.

import Definitions.Def_owmr_renewal
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem canonical_savings {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hk : 0 < k) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh) :
    ∃ (G : ℝ) (g : ℝ → ℝ), N.J i k = ENNReal.ofReal G ∧ (∀ x, g x = G - N.F i (Sh - x)) ∧
      Continuous g ∧ ConcaveOn ℝ Set.univ g ∧
      (∀ x ∈ Set.Icc 0 (Sh - sh), 0 ≤ g x ∧ g x ≤ G) ∧ g (Sh - sh) = 0 ∧
      IntegrableOn g (Set.Ico 0 (Sh - sh)) (renewalMeasure (N.marginal i)) ∧
      ∫ x in Set.Ico 0 (Sh - sh), g x ∂(renewalMeasure (N.marginal i)) = k ∧
      (∀ x ∈ Set.Icc 0 (Sh - sh), g x ≤ N.p * ((Sh - sh) - x)) ∧
      0 < G ∧
      (N.h ≤ N.H i → N.h * N.p / (N.h + N.p) * (Sh - sh) ≤ G) := by sorry
end OWMR
