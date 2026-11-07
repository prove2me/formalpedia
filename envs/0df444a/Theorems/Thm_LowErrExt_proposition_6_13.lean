-- Prove2me | Theorems.Thm_LowErrExt_proposition_6_13
-- name    : LowErrExt.proposition_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:18.897228+00:00
-- url     : https://prove2.me/theorems/0430ff57-7595-4771-a018-e2fb70f0ee6e
-- title:
--   Proposition 6.13 — finding spreadness: a dense subsource that is $(r,k)_\infty$-spread
-- statement:
--   Let $G$ be a finite abelian group with $n:=H_0[G]=\log|G|$, and let $\mathbf X$ be a source on $G$. For every $r>0$ and $k\ge0$ there is a coset $V\subseteq G$ with
--   $$\Pr[\mathbf X\in V]\ge 2^{-\ell},\qquad \ell:=\frac{nk}{r},$$
--   such that $\mathbf X|_{\mathbf X\in V}$ is $(r,k)_\infty$-spread in $V$.
--
--   Every source thus has a subsource of small deficiency that is spread; this is the first ingredient of the regularity theorem (Theorem 7.5).
--
--   Differences from the source:
--   - encoding: spreadness over all homomorphisms L out of G (Definition 6.2) → spreadness over the quotient maps G → G/K for subgroups K (IsSpread); reason: a homomorphism with kernel K is an injective map after π_K, so images and entropies agree (Observation 6.5's argument); same instances
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Proposition 6.13, p.41

import Mathlib
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsSpread

namespace LowErrExt

/-- **Proposition 6.13 (Finding spreadness).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Proposition 6.13, p.41: "Let X ∼ G, where G is a finite abelian group with n := H0[G]. For any r > 0
and k ≥ 0, there is some coset V ⊆ G with Pr[X ∈ V] ≥ 2^{−ℓ} such that X|X∈V is (r, k)∞-spread in V,
where ℓ := nk/r."

**Formalization Note.** `n = H0[G] = log₂|G|`; spreadness is over subgroup kernels (see
`IsSpreadBy`) and includes `supp(X|X∈V) ⊆ V`. No torsion hypothesis, as in the paper. -/
theorem proposition_6_13 {G : Type} [AddCommGroup G] [Fintype G] (X : PMF G) (r k : ℝ)
    (hr : 0 < r) (hk : 0 ≤ k) :
    ∃ V : Set G, IsCoset V ∧ (2 : ℝ) ^ (-(H0 (Set.univ : Set G) * k / r)) ≤ probOf X V ∧
      IsSpreadInf r k V (condOn X V) := by sorry

end LowErrExt
