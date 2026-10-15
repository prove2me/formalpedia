-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_sobolev_endpoint_embedding
-- name    : HunterPDE.Sobolev.sobolev_endpoint_embedding
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:21:46.903674+00:00
-- url     : https://prove2.me/theorems/8fb8843d-dba4-412a-b278-bfb39cea853b
-- title:
--   Sobolev endpoint embedding for weakly differentiable functions
-- statement:
--   Let $1\le p<n$ and $p^*=np/(n-p)$. There is a nonnegative constant $C$, chosen before the function, such that every $f\in W^{1,p}(\mathbb R^n)$ lies in $L^{p^*}(\mathbb R^n)$ and
--   $$\|f\|_{p^*}\le C\|f\|_{W^{1,p}}.$$
--   This is the endpoint step in the proof of Theorem 3.31: extend the compact smooth Gagliardo–Nirenberg–Sobolev inequality by the density theorem. The norm is the sum over multi-indices in Definition 3.23. No assertion about intermediate exponents is assumed.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, p. 66, Theorem 3.31, first two paragraphs of its proof; Theorems 3.24 and 3.28

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Definitions.Def_HunterPDE_Sobolev_SobolevConjugate

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.sobolev_endpoint_embedding {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) (hpn : p < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      MemW 1 (ENNReal.ofReal p) Set.univ f →
        MemLp f (ENNReal.ofReal (sobolevConjugate n p)) volume ∧
          eLpNorm f (ENNReal.ofReal (sobolevConjugate n p)) volume ≤
            (C : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by sorry
