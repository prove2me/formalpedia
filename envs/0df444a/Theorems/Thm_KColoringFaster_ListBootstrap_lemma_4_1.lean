-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_lemma_4_1
-- name    : KColoringFaster.ListBootstrap.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:06.522507+00:00
-- url     : https://prove2.me/theorems/80166a31-8488-49d0-b9f2-01def47378df
-- title:
--   Lemma 4.1 — seed shortening
-- statement:
--   Fix an integer $k\ge 2$ and a real $a$ with $1\le a<2$. In a $k$-list-coloring instance a vertex is **active** if its list has size exactly $k$; relative to a fixed witness list coloring $w$, an active vertex is **good** if some color in its list occurs on more than $\Delta_1$ of its neighbours in $w$, and **bad** otherwise.
--
--   There are constants $\beta_0>0$, $\Delta_1\in\mathbb N$, $C_S<2$ and $c>0$, depending only on $k$ and $a$, such that the following holds. Suppose $(k-1)$-list-coloring over arbitrary palettes has an algorithm of base $a$, that is, a randomized algorithm deciding list colorability of instances with all lists of size at most $k-1$ in time $O^*(a^n)$, with error at most $e^{-c'n}$ on both sides for some $c'>0$. Then there is an algorithm that, on every $k$-list-coloring instance over an arbitrary palette, runs in time
--   $$O^*\big(C_S^{\,n}\big)$$
--   on every coin string, and that, relative to every list coloring $w$ of the instance with at most $\beta_0 n$ bad active vertices, outputs a list coloring of the instance with probability at least $1-e^{-cn}$.
--
--   This is the "seed solver" of Theorem 5.1: it handles the instances in which almost every active vertex has a dominant color among its neighbours.
--
--   **Formalization Note** Algorithms and $O^*$ are as in the definition `Algorithms`.
--
--   Differences from the source:
--   - reading: constants "depending only on $k, a$" → $\beta_0,\Delta_1,C_S,c$ are chosen before the assumed $(k-1)$-list-coloring algorithm; reason: this is what "depending only on $k,a$" means
--   - reading: "probability at least $1-\exp(-\Theta(n))$" → at least $1-e^{-cn}$ for a constant $c>0$ depending only on $k,a$; reason: only the lower bound of $\Theta$ is a guarantee
--   - reading: "it returns a coloring" → the output is the encoding of some list coloring of the instance; reason: a returned coloring is a list coloring (the proof verifies it), not necessarily $w$
--   - reading: "(k − 1)-list-coloring has an algorithm of base $a$" → a randomized decision algorithm in time $O^*(a^n)$ with error at most $e^{-c'n}$ on both sides, for some $c'>0$; reason: §3 (p. 7) allows exponentially small error; two-sided error is the weakest hypothesis
--   - encoding: $\Delta_1$ a constant → $\Delta_1\in\mathbb N$; reason: "more than $\Delta_1$ neighbours" is the same condition for $\Delta_1$ and $\lfloor\Delta_1\rfloor$
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: arbitrary palette $P$ → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 12, Lemma 4.1 and the preceding paragraph of §4.1

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

open CongruencyTU

/-- Lemma 4.1 (Seed shortening), p. 12, with its preamble. Fix `k ≥ 2` and `1 ≤ a < 2`. There are
constants `β₀ > 0`, `Δ₁`, `C_S < 2` and `c > 0`, depending only on `k, a`, such that: if
`(k-1)`-list-coloring over arbitrary palettes has an algorithm of base `a` (randomized, error at most
`e^{-c' n}` on both sides for some `c' > 0`), then there is an algorithm that on every
`k`-list-coloring instance runs in `O*(C_S^n)` time on every coin string, and that, relative to every
list coloring `w` of the instance with at most `β₀ n` bad active vertices (an active vertex has a list
of size exactly `k`; it is bad if no color of its list occurs on more than `Δ₁` of its neighbours in
`w`), outputs a list coloring of the instance with probability at least `1 - e^{-c n}`. -/
theorem lemma_4_1 (k : ℕ) (hk : 2 ≤ k) (a : ℝ) (ha1 : 1 ≤ a) (ha2 : a < 2) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ Δ₁ : ℕ, ∃ CS : ℝ, CS < 2 ∧ ∃ c : ℝ, 0 < c ∧
      ((∃ c' : ℝ, 0 < c' ∧ RandDecides encList ListInstance.n (MaxListLE (k - 1)) ListColorable
          (fun I => a ^ I.n) (expErr c') (expErr c')) →
        ∃ (P : Program) (p q : Polynomial ℕ), ∀ I : ListInstance, MaxListLE k I →
          AllRunsBounded P q (encList I) (budget p (encList I) (CS ^ I.n)) ∧
          ∀ w : Fin I.n → ℕ, IsListColoring I w → (badCount k Δ₁ I w : ℝ) ≤ β₀ * I.n →
            1 - expErr c I.n ≤
              coinFrac P (encList I) (budget p (encList I) (CS ^ I.n)) (IsColoringOutput I)) := by sorry

end KColoringFaster.ListBootstrap
