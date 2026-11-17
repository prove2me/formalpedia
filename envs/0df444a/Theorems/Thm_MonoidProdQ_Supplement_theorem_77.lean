-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_77
-- name    : MonoidProdQ.Supplement.theorem_77
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:25:27.323896+00:00
-- url     : https://prove2.me/theorems/29646e53-3686-4dbf-ad77-27a6b8f0937c
-- title:
--   Theorem 77 — cube-root-size AGS bound (Result 3)
-- statement:
--   Let $L(n)=2+\log_2(n+2)$. There is a universal constant $C$ such that for every finite aperiodic monoid $M$ of order $N$ and every $n\ge1$,
--   $$Q_{1/3}(\mathrm{Prod}_{M,n})\le\min\Bigl\{n,\ \sqrt n\,L(n)^{C(N\log(N+2))^{1/3}}\Bigr\}\tag{70}$$
--   and
--   $$Q_{1/3}(\mathrm{Prod}_{M,n})\le\sqrt n\,\bigl(NL(n)\bigr)^{C(N\log(N+2))^{1/3}}.\tag{71}$$
--   Both estimates hold, with the same $C$, for every finite aperiodic semigroup $S$ after replacing $N$ by $|S|+1$.
--
--   The dependence on the monoid size enters only through $N^{1/3}$ up to logarithms in the exponent.
--
--   **Formalization Note** $\log$ is natural and $\log_2$ base two; the powers are real powers. For a semigroup, the product map is the published `FanInSemigroup.tupleProd`.
--
--   Differences from the source:
--
--   - encoding: universal constant C, the same estimates for semigroups → one ∃ C > 0 for (70), (71) and the semigroup clause; reason: the stated universality
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 77 (Cube-root-size AGS bound), p.92

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_FanInSemigroup_wordProd
import Definitions.Def_MonoidProdQ_Supplement_IsAperiodicSg

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 77 (Cube-root-size AGS bound),
p.92 (Result 3, p.8), with `L(n) = 2 + log₂(n + 2)` (§11, p.79; also p.17): "There is a universal constant
C such that, for every finite aperiodic monoid M of order N and every n ≥ 1,
Q_{1/3}(Prod_{M,n}) ≤ min{n, √n L(n)^{C(N log(N+2))^{1/3}}}. (70) Before the standard read-all
absorption, the proof gives the convenient form Q_{1/3}(Prod_{M,n}) ≤ √n (NL(n))^{C(N log(N+2))^{1/3}}.
(71) Consequently, if S is a finite aperiodic semigroup, the same estimates hold after replacing N
by |S| + 1." One universal `C > 0` for all three conjuncts: Eq. (70) and Eq. (71) for every
finite aperiodic monoid and `n ≥ 1`, and both estimates for every finite aperiodic semigroup `S`
and `n ≥ 1` with `N = |S| + 1`.

**Formalization Note.** `N = |M|`; `log` is natural, `log₂` is `Real.logb 2`, and the powers
are real powers. `Prod_{M,n}` is `prodMap univ n`; for a semigroup, `Prod_{S,n}` is the
published `FanInSemigroup.tupleProd` (the product of an `n`-tuple, `n ≥ 1`) and aperiodicity is
`IsAperiodicSg`. -/
theorem theorem_77 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
        ∀ n : ℕ, 1 ≤ n →
          (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (min (n : ℝ) (Real.sqrt n * (2 + Real.logb 2 (n + 2)) ^
                (C * ((Fintype.card M : ℝ) * Real.log (Fintype.card M + 2)) ^ ((1 : ℝ) / 3)))) ∧
            (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (Real.sqrt n *
                ((Fintype.card M : ℝ) * (2 + Real.logb 2 (n + 2))) ^
                  (C * ((Fintype.card M : ℝ) * Real.log (Fintype.card M + 2)) ^ ((1 : ℝ) / 3)))) ∧
      (∀ (S : Type u) [Semigroup S] [Fintype S] [DecidableEq S], IsAperiodicSg S →
        ∀ (n : ℕ) (hn : 1 ≤ n),
          (Q13 (FanInSemigroup.tupleProd (S := S) hn) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (min (n : ℝ) (Real.sqrt n * (2 + Real.logb 2 (n + 2)) ^
                (C * (((Fintype.card S + 1 : ℕ) : ℝ) *
                  Real.log ((Fintype.card S + 1 : ℕ) + 2)) ^ ((1 : ℝ) / 3)))) ∧
            (Q13 (FanInSemigroup.tupleProd (S := S) hn) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (Real.sqrt n *
                (((Fintype.card S + 1 : ℕ) : ℝ) * (2 + Real.logb 2 (n + 2))) ^
                  (C * (((Fintype.card S + 1 : ℕ) : ℝ) *
                    Real.log ((Fintype.card S + 1 : ℕ) + 2)) ^ ((1 : ℝ) / 3)))) := by sorry

end MonoidProdQ.Supplement
