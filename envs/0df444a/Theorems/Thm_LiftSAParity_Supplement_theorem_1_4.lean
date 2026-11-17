-- Prove2me | Theorems.Thm_LiftSAParity_Supplement_theorem_1_4
-- name    : LiftSAParity.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:18:37.49251+00:00
-- url     : https://prove2.me/theorems/47e1cd7e-013a-487c-9eb5-f0c04f7563f7
-- title:
--   Theorem 1.4 — every uSA(⊕) refutation of $\mathrm{BPHP}^m_n$ has size $2^{\Omega(n^{1/5})}$ for every $m>n$
-- statement:
--   There are a constant $c>0$ and a threshold $N_0$ such that, for every $k$ with $n=2^k\ge N_0$ and every number of pigeons $m>n$:
--
--   1. every semantic SA(⊕) refutation of $\mathrm{BPHP}^m_n$ has coefficient size at least $2^{c\,n^{1/5}}$;
--   2. every SA(⊕) refutation of $\mathrm{BPHP}^m_n$ has coefficient size at least $2^{c\,n^{1/5}}$.
--
--   So every uSA(⊕) refutation of the binary pigeonhole principle has size $2^{\Omega(n^{1/5})}$, both for $m=n+1$ and for the weak pigeonhole principle with arbitrarily many pigeons; the constant does not depend on $m$. Since uSA(⊕) p-simulates RevRes(⊕), this gives depth-unrestricted RevRes(⊕) lower bounds for binary PHP.
--
--   **Formalization Note** uSA(⊕) is SA(⊕) with size the coefficient size (p.4). $\mathrm{BPHP}^m_n$ is the collision CNF `bphp m k` over $m$ blocks of $k$ bits; $n^{1/5}$ is the real power $(2^k)^{1/5}$.
--
--   Differences from the source:
--   - reading: size 2^{Ω(n^{1/5})} → one c > 0 and one N₀, uniform in m > n, with bound 2^{c·n^{1/5}} for all n = 2^k ≥ N₀; reason: the standard meaning of Ω for an asymptotic bound in n; the proof (p.23) fixes r and t as functions of n only
--   - generalization: every uSA(⊕) refutation (SA(⊕) with coefficient size) → clause 1 for semantic SA(⊕) and clause 2 for SA(⊕), with the same c; reason: clause 2 is the printed bound; clause 1 adds the semantic system of p.9, to which the paper's proof (via Theorem 5.4) applies
--   - reading: BPHP^m_n (clauses not listed) → the collision CNF: for u ≠ u' and every hole a, the clause falsified exactly when both pigeons sit in a; reason: the standard encoding of "m pigeons cannot sit in n = 2^k holes" with k bits per pigeon
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §1.1, Theorem 1.4, p.5; proof §6.2, p.23

import Mathlib
import Definitions.Def_LiftSAParity_SemSAXorRefutation
import Definitions.Def_LiftSAParity_SAXorRefutation
import Definitions.Def_LiftSAParity_Supplement_bphp

namespace LiftSAParity

namespace Supplement

/-- **Theorem 1.4** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree to Unary
Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §1.1, p.5; proof §6.2, p.23):
"For every m > n, every uSA(⊕) refutation of BPHP^m_n has size 2^{Ω(n^{1/5})}."

There are `c > 0` and `N₀` such that for every `k` with `n = 2^k ≥ N₀` and every `m > n`:
(a) every semantic SA(⊕) refutation of `BPHP^m_n` has coefficient size at least `2^{c·n^{1/5}}`,
and (b) every SA(⊕) refutation of `BPHP^m_n` has coefficient size at least `2^{c·n^{1/5}}`.

**Formalization Note** uSA(⊕) is SA(⊕) with size the coefficient size (p.4). `2^{Ω(n^{1/5})}` is
read as one `c > 0`, uniform in `m`, valid for all `n ≥ N₀`. `BPHP^m_n` is the collision CNF
`bphp m k`. -/
theorem theorem_1_4 : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ k m : ℕ, N₀ ≤ 2 ^ k → 2 ^ k < m →
    (∀ π : SemSAXorRefutation (bphp m k),
        (2 : ℝ) ^ (c * ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 5)) ≤ π.coeffSize) ∧
    (∀ π : SAXorRefutation (bphp m k),
        (2 : ℝ) ^ (c * ((2 : ℝ) ^ k) ^ ((1 : ℝ) / 5)) ≤ π.coeffSize) := by sorry

end Supplement

end LiftSAParity
