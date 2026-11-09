-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_entire_product_coefficients
-- name    : MomentAmbiguitySecretary.Secretary.entire_product_coefficients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:08.228234+00:00
-- url     : https://prove2.me/theorems/baf7434e-cccd-437c-bac8-649334e0af72
-- title:
--   Lemma 8.7 — entire product and all coefficient formulas
-- statement:
--   Fix integers $B,N\ge2$ and put $q=1/B$. The products $G_{N,M}$ converge locally uniformly on $\mathbb C$ to the entire function $G_N$. Their Taylor expansions converge at every complex argument, and the finite coefficients satisfy
--
--   $$w_j^{(M)}=\sum_{\substack{0\le c_0,\ldots,c_M<N\\\sum c_a=j}}q^{\sum a c_a}.$$
--
--   For every $j\ge0$, these coefficients are nondecreasing in $M$ and converge to $w_j$, with both absolutely convergent occupancy formulas
--
--   $$w_j=\sum_{\substack{(c_a)\text{ finitely supported}\\0\le c_a<N,\ \sum c_a=j}}q^{\sum a c_a}=\sum_{\substack{(c_a)\text{ finitely supported}\\0\le c_a<N,\ \sum c_a=j}}B^{-\sum a c_a}.$$
--
--   This is the complete analytic and coefficient statement needed by the residue construction.
--
--   Differences from the source:
--   - encoding: coefficient and series notation → Taylor coefficients, finitely supported occupancies and HasSum; reason: the Taylor formulas identify the same coefficients and HasSum records convergence rather than relying on totalized infinite sums
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied preprint, Lemma 8.7, PDF/printed p.30, SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator

open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary

/-- Lemma 8.7, pinned preprint PDF/printed pp.30–31: all three clauses. -/
theorem entire_product_coefficients (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) :
    TendstoLocallyUniformlyOn (fun M : ℕ => finiteProduct B N M)
      (entireProduct B N) atTop univ ∧
    Differentiable ℂ (entireProduct B N) ∧
    (∀ M j : ℕ, finiteTaylor B N M j = (finiteOccupancySum B N M j : ℂ)) ∧
    (∀ M : ℕ, ∀ z : ℂ,
      HasSum (fun j : ℕ => finiteTaylor B N M j * z ^ j) (finiteProduct B N M z)) ∧
    (∀ z : ℂ, HasSum (fun j : ℕ => (coefficient B N j : ℂ) * z ^ j)
      (entireProduct B N z)) ∧
    (∀ j : ℕ, Monotone (fun M : ℕ => finiteOccupancySum B N M j) ∧
      Tendsto (fun M : ℕ => finiteOccupancySum B N M j) atTop (𝓝 (coefficient B N j)) ∧
      HasSum (fun c : Occupancy N j => ((B : ℝ)⁻¹) ^ occupancyExponent c)
        (coefficient B N j) ∧
      HasSum (fun c : Occupancy N j => (B : ℝ) ^ (-(occupancyExponent c : ℤ)))
        (coefficient B N j)) := by sorry

end MomentAmbiguitySecretary.Secretary
