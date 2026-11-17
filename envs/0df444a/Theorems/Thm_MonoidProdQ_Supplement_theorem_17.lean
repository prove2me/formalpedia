-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_17
-- name    : MonoidProdQ.Supplement.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:15:50.264794+00:00
-- url     : https://prove2.me/theorems/f8bc0137-02dc-4eeb-9796-2ddb314ac975
-- title:
--   Theorem 17 — log-free $\mathcal R$-trivial product bound $\mathrm{ADV}^\pm(\mathrm{Prod}_{M,n})\le8\sqrt{n\min\{n,D_R(M)\}}$
-- statement:
--   Let $M$ be a finite $\mathcal R$-trivial monoid and $D_R(M)$ its right-ideal depth. For every $n\ge1$:
--
--   1. $$\mathrm{ADV}^\pm(\mathrm{Prod}_{M,n})\le 8\sqrt{n\min\{n,D_R(M)\}};$$
--   2. $Q_{1/3}(\mathrm{Prod}_{M,n})\le C\min\{n,\sqrt{n\,D_R(M)}\}$ with a universal constant $C$;
--   3. more generally, for every nonempty promise set $D\subseteq M^n$ and $f(x)=x_1\cdots x_n$ on $D$, with $C_D=\max_{x\in D}|\{0\le i<n:p_i(x)\ne p_{i+1}(x)\}|$ the largest number of prefix-product changes,
--   $$\mathrm{ADV}^\pm(f)\le8\sqrt{nC_D},$$
--   and $\mathrm{ADV}^\pm(f)=0$ when $C_D=0$.
--
--   The bound depends on the depth of the right-ideal order rather than on $|M|$, which can be exponentially larger.
--
--   **Formalization Note** $\mathrm{Prod}_{M,n}$ is the published product map over the full alphabet, and $f$ is the same map restricted to $D$.
--
--   Differences from the source:
--
--   - encoding: O(min{n, √(n D_R(M))}) → ∃ universal C > 0 with Q_{1/3} ≤ C·min{n, √(n D_R(M))}; reason: an O-bound with a universal constant
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 17 (Log-free R-trivial product bound), p.32

import Definitions.Def_MonoidProdQ_IsRTrivial
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_rightIdealDepth
import Definitions.Def_MonoidProdQ_Supplement_prefixChangeBound

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 17 (Log-free R-trivial product
bound), p.32: "Let M be a finite R-trivial monoid. Then ADV±(Prod_{M,n}) ≤ 8√(n min{n, D_R(M)}),
Q_{1/3}(Prod_{M,n}) = O(min{n, √(nD_R(M))}). More generally, let ∅ ≠ D ⊆ Mⁿ and define
f : D → M by f(x) = x₁ ⋯ xₙ. Put C_D = max_{x∈D} |{0 ≤ i < n : pᵢ(x) ≠ pᵢ₊₁(x)}|. Then
ADV±(f) ≤ 8√(nC_D), with value zero when C_D = 0." Three conjuncts, for `n ≥ 1`:

1. `ADV±(Prod_{M,n}) ≤ 8√(n·min{n, D_R(M)})`;
2. one universal `C > 0` with `Q_{1/3}(Prod_{M,n}) ≤ C·min{n, √(n·D_R(M))}`;
3. for every nonempty promise set `D ⊆ Mⁿ`, `ADV±(f) ≤ 8√(n·C_D)`, and `ADV±(f) = 0` when
   `C_D = 0`.

**Formalization Note.** `Prod_{M,n}` is `prodMap univ n` (letters in the subtype `↥univ`), and
`f` is the same map with promise domain `D`. `D_R(M)` is `rightIdealDepth M`, `C_D` is
`prefixChangeBound D`. The R-triviality of `M` is kept as a hypothesis of the "more generally"
clause, which is stated inside the theorem's scope. -/
theorem theorem_17 :
    (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsRTrivial M →
      ∀ n : ℕ, 1 ≤ n →
        advPm (prodMap (Finset.univ : Finset M) n) Finset.univ ≤
          ENNReal.ofReal (8 * Real.sqrt (n * (min n (rightIdealDepth M) : ℕ)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsRTrivial M →
        ∀ n : ℕ, 1 ≤ n →
          (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal (C * min (n : ℝ) (Real.sqrt (n * rightIdealDepth M)))) ∧
    (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsRTrivial M →
      ∀ n : ℕ, 1 ≤ n → ∀ D : Finset (Fin n → (Finset.univ : Finset M)), D.Nonempty →
        advPm (prodMap (Finset.univ : Finset M) n) D ≤
            ENNReal.ofReal (8 * Real.sqrt (n * prefixChangeBound D)) ∧
          (prefixChangeBound D = 0 → advPm (prodMap (Finset.univ : Finset M) n) D = 0)) := by sorry

end MonoidProdQ.Supplement
