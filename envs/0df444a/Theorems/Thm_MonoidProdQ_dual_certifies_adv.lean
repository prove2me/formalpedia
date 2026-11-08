-- Prove2me | Theorems.Thm_MonoidProdQ_dual_certifies_adv
-- name    : MonoidProdQ.dual_certifies_adv
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:54:10.376691+00:00
-- url     : https://prove2.me/theorems/2290f731-5f56-417f-806c-da41f17cb12b
-- title:
--   Eqs. (3)–(4): an all-pairs dual of cost $T$ certifies $\mathrm{ADV}^{\pm}(f)\le T$
-- statement:
--   Let $I$ be a finite index set, $\Sigma$ and $O$ finite alphabets, $D\subseteq\Sigma^I$ a promise domain and $f$ a function with values in $O$. Suppose that vectors $u_{x,i},v_{y,i}\in\mathbb C^d$ ($x,y\in D$, $i\in I$) satisfy
--
--   $$\sum_{i:\,x_i\ne y_i}\langle u_{x,i},v_{y,i}\rangle=1[f(x)\ne f(y)]\qquad\text{for every } x,y\in D\tag{3}$$
--
--   and
--
--   $$\max\Big\{\max_x\sum_i\|u_{x,i}\|^2,\ \max_y\sum_i\|v_{y,i}\|^2\Big\}\le T.\tag{4}$$
--
--   Then $\mathrm{ADV}^{\pm}(f)\le T$.
--
--   This is how every upper bound of the paper is obtained: an explicit dual is built and its cost bounds the adversary value. (The converse quoted on the same page, that a dual of cost at most $2\,\mathrm{ADV}^{\pm}(f)$ exists [LMR+11], is a separate cited fact and is not part of this item.)
--
--   Differences from the source:
--   - reading: vectors over an unspecified field → vectors in $\mathbb C^d$ for some $d$; reason: the stronger reading: real vectors are complex vectors with the same inner products, so the statement covers the real case
--   - encoding: $\mathrm{ADV}^{\pm}$ and $Q_{1/3}$ as numbers → `ADV±` in `ℝ≥0∞`, $Q_{1/3}$ in `ℕ∞` (cast to `ℝ≥0∞`); reason: Lean convention; suprema and infima are never junk values, and both are finite in every instance
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eqs. (3)–(4), p.25

import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_DualFeasible
import Definitions.Def_MonoidProdQ_dualCost

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Eqs. (3)–(4), p.25: an all-pairs dual certifies the adversary bound — "Such
vectors certify ADV±(f) ≤ T". For finite index set `I`, finite input and output alphabets, a
promise domain `D` and `f`: if `u, v` satisfy Eq. (3) for every `x, y ∈ D` and their cost
(Eq. (4)) is at most `T`, then `ADV±(f) ≤ T`. (The converse direction quoted on the same page,
[LMR+11], is not part of this item.) -/
theorem dual_certifies_adv {I Sig Out : Type*} [Fintype I] [DecidableEq I] [Fintype Sig]
    [DecidableEq Sig] [Fintype Out] [DecidableEq Out] (f : (I → Sig) → Out)
    (D : Finset (I → Sig)) (d : ℕ) (u v : D → I → EuclideanSpace ℂ (Fin d)) (T : ℝ)
    (hfeas : DualFeasible f D u v) (hcost : (dualCost u v : ℝ) ≤ T) :
    advPm f D ≤ ENNReal.ofReal T := by sorry

end MonoidProdQ
