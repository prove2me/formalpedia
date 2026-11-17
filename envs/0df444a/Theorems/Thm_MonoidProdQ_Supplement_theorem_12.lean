-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_12
-- name    : MonoidProdQ.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:13:39.242991+00:00
-- url     : https://prove2.me/theorems/6ebfa589-94c7-4dfd-bd4f-9fe544bbd127
-- title:
--   Theorem 12 — fixed finite-monoid trichotomy: $\Theta_S(n)$ for nonaperiodic semigroups; $0$, $\tilde\Theta_M(\sqrt n)$, $\Theta_M(n)$ for monoids
-- statement:
--   Write $\mathrm{Prod}_{S,n}:S^n\to S$ for the ordered product map and $Q_{1/3}$ for bounded-error quantum query complexity, one query revealing a whole letter.
--
--   1. Let $S$ be a finite nonaperiodic semigroup. There are constants $c_S,C_S>0$ such that for every $n\ge1$
--   $$c_S\,n\le Q_{1/3}(\mathrm{Prod}_{S,n})\le C_S\,n,$$
--   and there is one Boolean postprocessing $h:S\to\{0,1\}$ with $c_S\,n\le Q_{1/3}(h\circ\mathrm{Prod}_{S,n})$ for every $n\ge1$.
--   2. If $M$ is a monoid with $|M|=1$, then $Q_{1/3}(\mathrm{Prod}_{M,n})=0$.
--   3. There is a universal $c>0$ such that every nontrivial finite aperiodic monoid $M$ satisfies $Q_{1/3}(\mathrm{Prod}_{M,n})\ge c\sqrt n$ for all $n\ge1$.
--   4. For every nontrivial finite aperiodic monoid $M$ there are $C_M>0$ and $e_M\in\mathbb N$ with
--   $$Q_{1/3}(\mathrm{Prod}_{M,n})\le C_M\sqrt n\,\bigl(\log(n+2)\bigr)^{e_M}\qquad(n\ge1).$$
--   5. For every finite nonaperiodic monoid $M$ there are $c_M,C_M>0$ with $c_M n\le Q_{1/3}(\mathrm{Prod}_{M,n})\le C_M n$ for all $n\ge1$.
--
--   This classifies the product problem of every fixed finite monoid: trivial, nearly square-root, or linear, according to whether $M$ is trivial, aperiodic, or contains a nontrivial group.
--
--   **Formalization Note** $Q_{1/3}$ is the published bounded-error query complexity (in $\mathbb N\cup\{\infty\}$); the semigroup product of an $n$-tuple ($n\ge1$) is the published `FanInSemigroup.tupleProd`. $\log$ is natural.
--
--   Differences from the source:
--
--   - encoding: Θ_S(n), Θ_M(n) → ∃ c, C > 0 depending on S (resp. M), for all n ≥ 1; reason: a subscript means the constants may depend on that object (Conventions, p.23)
--   - reading: the lower bound already holds for a Boolean postprocessing of the product → one h : S → Bool chosen before n, with c_S·n ≤ Q_{1/3}(h ∘ Prod_{S,n}) for every n ≥ 1, same c_S; reason: the stronger of the two readings (h fixed rather than chosen per n); it holds with h the indicator of the identity of a nontrivial subgroup
--   - reading: an Ω(√n) lower bound (no subscript) → one universal c > 0 chosen before M; reason: no subscript, and the proof is a uniform OR lower bound
--   - encoding: O_M(√n (log(n + 2))^{O_M(1)}) → ∃ C > 0 and e ∈ ℕ depending on M with Q_{1/3} ≤ C·√n·(log(n + 2))^e; reason: log(n + 2) > 1, so any real exponent can be rounded up to a natural one
--   - encoding: |M| = 1; nontrivial → Fintype.card M = 1; 1 < Fintype.card M; reason: same instances
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 12 (Fixed finite-monoid trichotomy), p.25

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_FanInSemigroup_wordProd
import Definitions.Def_MonoidProdQ_Supplement_IsAperiodicSg

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 12 (Fixed finite-monoid
trichotomy), p.25: "Let S be a finite nonaperiodic semigroup. Then Q_{1/3}(Prod_{S,n}) = Θ_S(n).
The lower bound already holds for a Boolean postprocessing of the product. Consequently, for
every fixed finite monoid M, Q_{1/3}(Prod_{M,n}) = 0 if |M| = 1; Θ̃_M(√n) if M is nontrivial and
aperiodic; Θ_M(n) if M is nonaperiodic. Here Θ̃_M(√n) means an Ω(√n) lower bound and an
O_M(√n (log(n + 2))^{O_M(1)}) upper bound." Five conjuncts:

1. finite nonaperiodic semigroup `S`: constants `c, C > 0` depending on `S` with
   `c·n ≤ Q_{1/3}(Prod_{S,n}) ≤ C·n` for every `n ≥ 1`, and one Boolean postprocessing
   `h : S → Bool` with `c·n ≤ Q_{1/3}(h ∘ Prod_{S,n})` for every `n ≥ 1`;
2. `|M| = 1`: `Q_{1/3}(Prod_{M,n}) = 0`;
3. nontrivial aperiodic `M`: `c·√n ≤ Q_{1/3}(Prod_{M,n})` with one `c > 0` for all such `M`;
4. nontrivial aperiodic `M`: `Q_{1/3}(Prod_{M,n}) ≤ C·√n·(log(n + 2))^e` with `C`, `e`
   depending on `M`;
5. nonaperiodic `M`: `c·n ≤ Q_{1/3}(Prod_{M,n}) ≤ C·n` with `c, C > 0` depending on `M`.

**Formalization Note.** `Prod_{S,n}` for a semigroup is the published
`FanInSemigroup.tupleProd` (the product `x₁ ⋯ xₙ` of an `n`-tuple, `n ≥ 1`), and `Prod_{M,n}`
for a monoid is `prodMap univ n`; the
promise domain is all of `Sⁿ` (resp. `Mⁿ`). The Boolean postprocessing is one fixed map,
chosen before `n` (the stronger of the two readings of "a Boolean postprocessing"; it holds
with `h` the indicator of the identity `e` of a nontrivial subgroup, using layers whose weight
is a multiple of the order of `g`). `log` is natural. `Q_{1/3}` is in `ℕ∞`,
compared in `ℝ≥0∞`. -/
theorem theorem_12 :
    (∀ (S : Type u) [Semigroup S] [Fintype S] [DecidableEq S], ¬ IsAperiodicSg S →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        (∀ (n : ℕ) (hn : 1 ≤ n),
          ENNReal.ofReal (c * n) ≤ (Q13 (FanInSemigroup.tupleProd (S := S) hn) Finset.univ : ℝ≥0∞) ∧
          (Q13 (FanInSemigroup.tupleProd (S := S) hn) Finset.univ : ℝ≥0∞) ≤ ENNReal.ofReal (C * n)) ∧
        ∃ h : S → Bool, ∀ (n : ℕ) (hn : 1 ≤ n),
          ENNReal.ofReal (c * n) ≤
            (Q13 (h ∘ FanInSemigroup.tupleProd (S := S) hn) Finset.univ : ℝ≥0∞)) ∧
    (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], Fintype.card M = 1 →
      ∀ n : ℕ, 1 ≤ n → Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ = 0) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], 1 < Fintype.card M →
        IsAperiodic M → ∀ n : ℕ, 1 ≤ n →
          ENNReal.ofReal (c * Real.sqrt n) ≤
            (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞)) ∧
    (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], 1 < Fintype.card M →
      IsAperiodic M → ∃ (C : ℝ) (e : ℕ), 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
          ENNReal.ofReal (C * Real.sqrt n * Real.log (n + 2) ^ e)) ∧
    (∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], ¬ IsAperiodic M →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (c * n) ≤ (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ∧
        (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤ ENNReal.ofReal (C * n)) := by sorry

end MonoidProdQ.Supplement
