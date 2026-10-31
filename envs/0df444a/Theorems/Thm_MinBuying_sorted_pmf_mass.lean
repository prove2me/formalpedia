-- Prove2me | Theorems.Thm_MinBuying_sorted_pmf_mass
-- name    : MinBuying.sorted_pmf_mass
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T18:08:59.255+00:00
-- url     : https://prove2.me/theorems/ce934f9b-b919-4aaa-8746-63ac52a81f31
-- title:
--   Exact probability mass of sorted exchangeable valuations, including ties
-- statement:
--   Let $w$ be an exchangeable probability mass function on $\mathbb R^n$, and sort each valuation vector into nondecreasing order. For a nondecreasing vector $v$, let $m_x(v)$ denote the multiplicity of coordinate value $x$. The sorted law has mass
--   $$\Pr(\operatorname{sort}(V)=v)=\frac{n!}{\prod_{x\in\{v_1,\ldots,v_n\}}m_x(v)!}\,w(v).$$
--   At a vector that is not nondecreasing, the sorted law has mass zero. The formula applies to arbitrary countable support and includes ties, supplying the exact orbit factor needed for the MTP2 order-statistic argument.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, https://doi.org/10.2139/ssrn.5178133 . Supporting finite-law lemma for the affiliation argument in Theorem 2. The proof reuses Mathlib permutation orbit-stabilizer and DomMulAct.stabilizer_card'.

import Definitions.Def_MinBuying_Symmetry

open scoped BigOperators

namespace MinBuying

/-- Exact mass of sorted exchangeable valuations, including ties. The orbit
size is n! divided by the product of the repeated-value multiplicity factorials. -/
theorem sorted_pmf_mass (n : ℕ) (w : PMF (Valuations n))
    (hex : Exchangeable w.toMeasure) :
    ∀ v : Valuations n,
      (Monotone v →
        ((w.map (fun z => z ∘ Tuple.sort z)) v).toReal =
          ((n.factorial : ℝ) /
            (∏ x ∈ Finset.univ.image v,
              (((Finset.univ.filter (fun i : Fin n => v i = x)).card).factorial : ℝ))) *
            (w v).toReal) ∧
      (¬ Monotone v → (w.map (fun z => z ∘ Tuple.sort z)) v = 0) := by
  sorry

end MinBuying
