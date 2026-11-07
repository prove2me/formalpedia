-- Prove2me | Theorems.Thm_LowErrExt_corollary_7_22
-- name    : LowErrExt.corollary_7_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:53:35.365203+00:00
-- url     : https://prove2.me/theorems/83afc227-407e-4cad-902f-0bb87f455876
-- title:
--   Corollary 7.22 — finding block-spreadness
-- statement:
--   Let $G$ be a finite abelian group with $t:=H_0[G]$, let $n\ge1$, and let $\mathbf X$ be a source on $G^n$. For every $k\ge0$ there is a coset $V\subseteq G^n$ with
--   $$\Pr[\mathbf X\in V]\ge 2^{-\ell},\qquad \ell:=tk,$$
--   such that $\mathbf X|_{\mathbf X\in V}$ is $(k)_\infty$-block-spread.
--
--   This is the second ingredient of Theorem 7.5's proof.
--
--   Differences from the source:
--   - encoding: block-spreadness over all homomorphisms L out of G (Definition 7.8) → over the quotient maps G → G/K applied coordinatewise (IsBlockSpread); reason: a homomorphism with kernel K is an injective map after π_K; constancy and entropy agree; same instances
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Corollary 7.22, p.67 (= Proposition 7.9, p.53)

import Mathlib
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_IsCoset
import Definitions.Def_LowErrExt_IsBlockSpread

namespace LowErrExt

/-- **Corollary 7.22 (Finding block-spreadness).**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Corollary 7.22, p.67 (restated as Proposition 7.9, p.53): "Let X ∼ Gⁿ, where G is a finite abelian
group with t := H0[G]. For any k ≥ 0, there is some coset V ⊆ Gⁿ with Pr[X ∈ V] ≥ 2^{−ℓ} such that
X|X∈V is (k)∞-block-spread, where ℓ := tk."

**Formalization Note.** `Gⁿ` is `Fin n → G` with `n ∈ ℕ = {1, 2, …}` (p.10); `t = log₂|G|`. -/
theorem corollary_7_22 {G : Type} [AddCommGroup G] [Fintype G] {n : ℕ} (hn : 0 < n)
    (X : PMF (Fin n → G)) (k : ℝ) (hk : 0 ≤ k) :
    ∃ V : Set (Fin n → G), IsCoset V ∧
      (2 : ℝ) ^ (-(H0 (Set.univ : Set G) * k)) ≤ probOf X V ∧
      IsBlockSpreadInf k (condOn X V) := by sorry

end LowErrExt
