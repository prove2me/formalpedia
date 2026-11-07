-- Prove2me | Theorems.Thm_KServerConj_eq_2
-- name    : KServerConj.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:50:32.950854+00:00
-- url     : https://prove2.me/theorems/426ef823-5683-4843-afbe-c89a20c9c2c6
-- title:
--   Equation (2) — the work function recurrence $w_t(X)=\min_{x\in X}\{w_{t-1}(X-x+r_t)+d(r_t,x)\}$
-- statement:
--   Let $(M,d)$ be a pseudometric space, $k\ge1$, $C_0$ a configuration of $k$ points and $r_1,r_2,\dots$ requests. The work function, defined as an offline optimum, satisfies $w_0(X)=D(C_0,X)$ for every configuration $X$ of $k$ points, and for every $t\ge1$ and every configuration $X$ of $k$ points
--
--   $$w_t(X)=\min_{x\in X}\big\{w_{t-1}(X-x+r_t)+d(r_t,x)\big\},$$
--
--   where $X-a+b=(X\setminus\{a\})\cup\{b\}$ and terms with $|X-x+r_t|<k$ count as $+\infty$. That is:
--
--   1. $w_t(X)\le w_{t-1}(X-x+r_t)+d(r_t,x)$ for every admissible $x\in X$, and
--   2. equality holds for some admissible $x\in X$,
--
--   where $x$ is admissible when $r_t\notin X$ or $x=r_t$.
--
--   The recurrence makes the work function computable online; it is what the row replacement of §2 encodes algebraically (Lemma 2.3).
--
--   Differences from the source:
--   - generalization: a metric space (M, d) → a pseudometric space (`PseudoMetricSpace M`); reason: the paper, p.1: "our proof works also when d is a pseudometric"; every metric space is a pseudometric space
--   - generalization: M finite (the analysis assumption, p.1) → M arbitrary; reason: the recurrence holds on every space; the finite case is a special case
--   - encoding: min over x ∈ X with the convention w_t(Y) = ∞ if |Y| < k → ≤ for every admissible x and = for some admissible x, admissible meaning r_t ∉ X or x = r_t; reason: the excluded terms are exactly those the convention makes ∞
--   - encoding: k servers and a configuration C₀ → hypotheses 1 ≤ k and C₀.card = k; reason: configurations are k-element sets; for k = 0 no configuration contains a request
--   - encoding: a finite request sequence r₁, …, r_T → r : ℕ → M, with requests r 1, …, r T; reason: values of r outside 1, …, T enter no quantity of the statement
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, equation (2), p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_workFn

namespace KServerConj

/-- **Equation (2): the work function recurrence.** Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, printed p.2
(PDF p.3): "the work function can be computed online by dynamic programming, via w₀(X) = D(C₀, X)
and the recurrence w_t(X) = min_{x∈X} {w_{t−1}(X − x + r_t) + d(r_t, x)}, (2) where
X − a + b := (X \ {a}) ∪ {b} and we use the convention w_t(Y) = ∞ if |Y| < k."

**Formalization Note.** The work function `workFn` is the offline optimum (its definition), so
both clauses are theorems. The minimum in (2) is written as "`≤` for every admissible `x`, `=` for
some admissible `x`". A point `x ∈ X` is admissible when `X − x + r_t` has `k` points, i.e.
`r_t ∉ X` or `x = r_t`; the excluded terms are exactly those the paper's convention makes `∞`.
The metric space is arbitrary (possibly infinite) and `d` may be a pseudometric. -/
theorem eq_2 {M : Type*} [PseudoMetricSpace M] [DecidableEq M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) :
    (∀ X : Finset M, X.card = k → workFn k C₀ r 0 X = confDist C₀ X) ∧
    ∀ t : ℕ, 1 ≤ t → ∀ X : Finset M, X.card = k →
      (∀ x ∈ X, (r t ∉ X ∨ x = r t) →
        workFn k C₀ r t X ≤ workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x) ∧
      ∃ x ∈ X, (r t ∉ X ∨ x = r t) ∧
        workFn k C₀ r t X = workFn k C₀ r (t - 1) (insert (r t) (X.erase x)) + dist (r t) x := by sorry

end KServerConj
