-- Prove2me | Theorems.Thm_KSPolySign_lemma_5_2
-- name    : KSPolySign.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:41:35.46455+00:00
-- url     : https://prove2.me/theorems/6b71532f-8ab2-40f4-8cb3-db55dbf0481d
-- title:
--   Lemma 5.2 — square-root certificate
-- statement:
--   Let $y$ be a light state and $F,B,\mathfrak u,\mathfrak q,\mathfrak z$ the scalar quantities of Definition 3.20 at an active coordinate.
--
--   1. $F>0$, $B>0$, $\mathfrak u>0$, $\mathfrak z>0$ and $\mathfrak u^2-F\mathfrak q>0$.
--   2. $F,B,\mathfrak u,\mathfrak z$ are uniformly bounded above and away from zero: there are constants $0<c\le C$ with $c\le F,B,\mathfrak u,\mathfrak z\le C$ at every active coordinate of every light state.
--
--   These inequalities make the covariance weights of Lemma 5.3 positive and give its strict margin.
--
--   **Formalization Note** At an active coordinate all these quantities are functions of $(y_i,u_i,v_i)$, where $|y_i|<1$, $u_i,v_i>0$ and the two light inequalities hold. The lemma is stated for every such triple.
--
--   Differences from the source:
--   - generalization: an active coordinate of a light state → every scalar triple (y, u, v) with |y| < 1, u, v > 0, ιβ(y)u < 1 + y, ιβ(y)v < 1 − y; reason: every quantity of Definition 3.20 depends only on (y_i, u_i, v_i), which form such a triple (u_i, v_i > 0 since U, V ≻ 0, a_i ≠ 0); the proof (p.45) works on this rectangle
--   - reading: uniformly bounded above and away from zero → one pair of constants 0 < c, C for all four quantities and all triples; reason: the proof (p.46) produces such c = 1/(400·2¹⁰) and C
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 5.2, p.45 (PDF p.45)

import Mathlib
import Definitions.Def_KSPolySign_certZ
import Definitions.Def_KSPolySign_certQ
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma 5.2 (Square-root certificate).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 5.2, p.45 (PDF p.45).

At a light state, the scalar quantities of Definition 3.20 satisfy (a) `F > 0`, `B > 0`, `𝔲 > 0`,
`𝔷 > 0`, `𝔲² − F𝔮 > 0`, and (b) `F, B, 𝔲, 𝔷` are uniformly bounded above and away from zero.

**Formalization Note** At an active coordinate `i` of a light state every quantity of Definition 3.20
is a function of `(y, u, v) = (y_i, u_i, v_i)`, where `|y| < 1`, `u, v > 0` (`U, V ≻ 0`, `a_i ≠ 0`) and
`ιβ(y)u < 1 + y`, `ιβ(y)v < 1 − y` (Definition 3.9). The lemma is stated for every such triple; one pair
of constants `c, C` serves all four quantities and all triples ("uniformly"). -/
theorem lemma_5_2 :
    (∀ y u v : ℝ, |y| < 1 → 0 < u → 0 < v → iota * beta y * u < 1 + y → iota * beta y * v < 1 - y →
      0 < certF y u v ∧ 0 < certB y u v ∧ 0 < certU y u v ∧ 0 < certZ y u v ∧
        0 < certU y u v ^ 2 - certF y u v * certQ y u v) ∧
    ∃ c C : ℝ, 0 < c ∧ ∀ y u v : ℝ, |y| < 1 → 0 < u → 0 < v → iota * beta y * u < 1 + y → iota * beta y * v < 1 - y →
      (c ≤ certF y u v ∧ certF y u v ≤ C) ∧ (c ≤ certB y u v ∧ certB y u v ≤ C) ∧
        (c ≤ certU y u v ∧ certU y u v ≤ C) ∧ (c ≤ certZ y u v ∧ certZ y u v ≤ C) := by sorry

end KSPolySign
