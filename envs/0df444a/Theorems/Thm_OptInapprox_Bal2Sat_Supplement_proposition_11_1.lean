-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_proposition_11_1
-- name    : OptInapprox.Bal2Sat.Supplement.proposition_11_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:02:13.032088+00:00
-- url     : https://prove2.me/theorems/95ec03ce-b005-4100-84e1-9d14e1a0925f
-- title:
--   Proposition 11.1 — q-ary noise acts diagonally on the orthogonal subset components
-- statement:
--   Let $q\ge2$, let $n,d$ be arbitrary nonnegative integers and let $f:[q]^n\to\mathbb R^d$. For every $-1/(q-1)\le\rho\le1$, the noise operator defined by conditional expectation satisfies
--
--   $$T_\rho(f)=\sum_{S\subseteq[n]}\rho^{|S|}f_S,$$
--
--   where $f_S$ is the orthogonal projection onto the source's subset subspace $X_S$ for the uniform product inner product. Every subset, including the empty and full subsets, occurs. The equality is one of vector-valued functions, with no boundedness, balance or simplex-range hypothesis. This supplies the noise-spectrum statement used in the q-ary hardness analysis.
--
--   Differences from the source:
--   - encoding: the uniform L² orthogonal projection f_S → starProjection in flattened Euclidean coordinates onto dependence-on-S orthogonal to proper-subset dependence spaces; reason: the inner products differ by positive q^(-n), leaving orthogonal projections unchanged, and the proper-subset dependence spaces are spanned by their subset components
--   - encoding: subsets of [n] and values in ℝ^d → all Finset (Fin n), with values Fin d → ℝ, also for n=0 or d=0; reason: zero-based indices and the zero-dimensional cases preserve the finite-dimensional identity
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 29, Proposition 11.1; context pp. 27–29

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Qary

namespace OptInapprox.Bal2Sat.Supplement

theorem proposition_11_1 (q : ℕ) (hq : 2 ≤ q) (n d : ℕ)
    (ρ : ℝ) (hρ : -(1 / ((q : ℝ) - 1)) ≤ ρ ∧ ρ ≤ 1)
    (f : QCube q n → Fin d → ℝ) :
    qNoise ρ f = fun x j =>
      ∑ S : Finset (Fin n), ρ ^ S.card * subsetComponent f S x j := by sorry

end OptInapprox.Bal2Sat.Supplement
