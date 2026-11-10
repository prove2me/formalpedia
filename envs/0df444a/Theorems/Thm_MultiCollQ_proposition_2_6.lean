-- Prove2me | Theorems.Thm_MultiCollQ_proposition_2_6
-- name    : MultiCollQ.proposition_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:56.391202+00:00
-- url     : https://prove2.me/theorems/1c391f4f-1a64-46a1-8e3b-4cb49c0ff13c
-- title:
--   Proposition 2.6 — exact sampling of a prescribed type: $c_\lambda$ representations and $|F_{\lambda,q}|\,c_\lambda=N!\,(q)_h$
-- statement:
--   Let $\lambda=(1^{n_1},\dots,k^{n_k})$ be an exact type, let the public buckets $Q_1,\dots,Q_h$ partition $[N]$ with size multiset $\lambda$, and let $b(y)$ be the index of the bucket containing $y$. For a permutation $\pi\in S_N$ and an injective label assignment $a:[h]\hookrightarrow\mathbb Z_q$ put
--
--   $$
--   f_{\pi,a}(x)=a(b(\pi(x))).
--   $$
--
--   Then:
--
--   1. every $f_{\pi,a}$ has exact type $\lambda$;
--   2. every $f\in F_{\lambda,q}$ has exactly $c_\lambda=\prod_{i=1}^{k}n_i!\,(i!)^{n_i}$ representations $f=f_{\pi,a}$;
--   3. $|F_{\lambda,q}|\cdot c_\lambda=N!\,(q)_h$, where $(q)_h=q(q-1)\cdots(q-h+1)$ is the falling factorial.
--
--   In particular, for uniform independent $\pi$ and $a$, $f_{\pi,a}$ is uniform over $F_{\lambda,q}$. This is the exact reduction from functions of a prescribed type to random permutations used by Theorem 2.7.
--
--   **Formalization Note** $(q)_h$ is `q.descFactorial h`. Representations are counted as pairs $(\pi,a)$ in `Equiv.Perm (Fin N) × (Fin h ↪ ZMod q)`.
--
--   Differences from the source:
--   - generalization: the standing hypotheses of §2.4, $N\ge3$ and $q\ge h$ → not assumed; reason: the three clauses hold for every $N$ and $q$ (for $q<h$ both sides of clause 3 are $0$ and $F_{\lambda,q}=\emptyset$); the source's case is the special case
--   - encoding: $|F_{\lambda,q}|=N!(q)_h/c_\lambda$ → $|F_{\lambda,q}|\cdot c_\lambda=N!\,(q)_h$; reason: $c_\lambda\ge1$, so the two are equivalent and the division is avoided
--   - encoding: $f_{\pi,a}$ is uniform over $F_{\lambda,q}$ → clauses 1 and 2; reason: the pushforward of the uniform measure on pairs is uniform on $F_{\lambda,q}$ exactly when every $f_{\pi,a}$ lies in $F_{\lambda,q}$ and every $f$ has the same number of representations
--   - encoding: $[N]$, $[h]$, $\mathbb Z_q$ → `Fin N`, `Fin h` (0-based), `ZMod q` with `[NeZero q]`; reason: Lean convention; same instances ($q\ge1$ on every range used)
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; PDF sha256 e20a0870…), Proposition 2.6, pp.13–14 (with (2.8), p.13)

import Mathlib
import Definitions.Def_MultiCollQ_HasExactType
import Definitions.Def_MultiCollQ_levelCount

namespace MultiCollQ

/-- Proposition 2.6 (Exact sampling of a prescribed type) (Peng, Hou, Dong, *Quantum multi-collision
lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), pp.13–14). Let the public buckets
`b : [N] → [h]` have size multiset `λ = (1^{n_1}, …, k^{n_k})` and put `f_{π,a}(x) = a(b(π(x)))`
(2.8) for `π ∈ S_N` and an injective label assignment `a : [h] ↪ Z_q`. Then (i) every `f_{π,a}` has
exact type `λ`; (ii) every `f ∈ F_{λ,q}` has exactly `c_λ = ∏_{i=1}^k n_i! (i!)^{n_i}`
representations `f = f_{π,a}`; (iii) `|F_{λ,q}| · c_λ = N! (q)_h`.

**Formalization Note.** `(q)_h` is `q.descFactorial h`. (iii) is the paper's
`|F_{λ,q}| = N!(q)_h / c_λ` multiplied out (`c_λ ≥ 1`). The section's standing hypotheses `N ≥ 3`
and `q ≥ h` are not assumed: the three clauses hold without them (for `q < h` both sides of (iii)
are `0`). Uniformity of `f_{π,a}` over `F_{λ,q}` is (i) together with (ii). -/
theorem proposition_2_6 {N h q k : ℕ} [NeZero q] (n : ℕ → ℕ) (b : Fin N → Fin h)
    (hb : HasBucketType b k n) :
    (∀ (π : Equiv.Perm (Fin N)) (a : Fin h ↪ ZMod q), HasExactType k n (fun x => a (b (π x)))) ∧
    (∀ f ∈ exactTypeSet N q k n,
      (Finset.univ.filter fun p : Equiv.Perm (Fin N) × (Fin h ↪ ZMod q) =>
          ∀ x, p.2 (b (p.1 x)) = f x).card =
        ∏ i ∈ Finset.Icc 1 k, (n i).factorial * (i.factorial) ^ (n i)) ∧
    (exactTypeSet N q k n).card * ∏ i ∈ Finset.Icc 1 k, (n i).factorial * (i.factorial) ^ (n i) =
      N.factorial * q.descFactorial h := by sorry

end MultiCollQ
