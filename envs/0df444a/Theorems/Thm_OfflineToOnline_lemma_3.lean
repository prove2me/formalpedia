-- Prove2me | Theorems.Thm_OfflineToOnline_lemma_3
-- name    : OfflineToOnline.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:33:27.965195+00:00
-- url     : https://prove2.me/theorems/ab8adbd6-2ce9-4397-b27c-73902b3bd46c
-- title:
--   Lemma 3 — $\frac1{2(q-1)}\|x\|_q^2$ is $1$-strongly convex w.r.t. $\ell_q$ for $q\in(1,2)$
-- statement:
--   For every $d$ and every $q\in(1,2)$, the function
--
--   $$
--   f(x)=\frac{1}{2(q-1)}\,\|x\|_q^2,\qquad \|x\|_q=\Big(\sum_{j=1}^d|x_j|^q\Big)^{1/q},
--   $$
--
--   is $1$-strongly convex on $\mathbb R^d$ with respect to the $\ell_q$ norm: $f(a x+b y)\le a f(x)+b f(y)-\frac{ab}{2}\|x-y\|_q^2$ for $a,b\ge0$, $a+b=1$.
--
--   It is the source of the strongly convex regularizer whose $\ell_1$ modulus gives the $\sqrt{\log d}$ rate of Theorem 1.
--
--   Differences from the source:
--   - reading: strongly convex (no modulus given) → strongly convex with modulus 1; reason: Inequality (1) on p.47 uses Lemma 3 with modulus 1
--   - encoding: ℓq norm defined as (x_1^q + x_w^q + … + x_d^q)^{1/q} → the norm of PiLp q, (∑_j |x_j|^q)^{1/q}; reason: x_w is a typo for x_2 and absolute values are needed for the ℓq norm
--   - encoding: q ∈ (1,2) real → q an extended nonnegative real with 1 < q < 2; reason: the same values; PiLp is indexed by extended reals
-- source:
--   Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, Online Learning via Offline Greedy Algorithms: Applications in Market Design and Optimization, arXiv:2102.11050v4, Lemma 3, p.47

import Mathlib

namespace OfflineToOnline

/-- **Lemma 3** (Shalev-Shwartz 2007). For `q ∈ (1, 2)`, the function
`f(x) = ‖x‖_q² / (2(q − 1))` on `ℝ^d` is (1-)strongly convex with respect to the `ℓq` norm.

Niazadeh, Golrezaei, Wang, Susan & Badanidiyuru, arXiv:2102.11050v4, Lemma 3, p.47.

Formalization Note: `ℝ^d` with the `ℓq` norm is `PiLp q (fun _ : Fin d => ℝ)`; `q` is an
extended nonnegative real with `1 < q < 2` (so it is finite). The page's "strongly convex" carries no
modulus; it is read as modulus `1`, which is how Inequality (1) on p.47 uses it. The printed
`ℓq` norm `(x_1^q + x_w^q + … + x_d^q)^{1/q}` is the usual one, `(∑ |x_j|^q)^{1/q}`. -/
theorem lemma_3 (d : ℕ) (q : ENNReal) [Fact (1 ≤ q)] (hq1 : 1 < q) (hq2 : q < 2) :
    StrongConvexOn Set.univ 1
      (fun x : PiLp q (fun _ : Fin d => ℝ) => ‖x‖ ^ 2 / (2 * (q.toReal - 1))) := by sorry

end OfflineToOnline
