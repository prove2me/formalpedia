-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_lemma_3_1
-- name    : KColoringFaster.ListBootstrap.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:48.991339+00:00
-- url     : https://prove2.me/theorems/7d316bfe-70ec-4155-9243-189583133134
-- title:
--   Lemma 3.1 — decision-to-search for list coloring
-- statement:
--   Let $\mathcal D$ be a class of list-coloring instances that is closed under singleton restriction: whenever $(G,L)\in\mathcal D$, $v\in V(G)$ and $c\in L(v)$, the instance obtained by replacing $L(v)$ with $\{c\}$ is in $\mathcal D$. (For a fixed palette $P$, the class of instances with all lists inside $P$ is such a class.) Let $T:\mathbb N\to\mathbb R$ be a time bound with $T(n)\ge 1$.
--
--   Suppose that list colorability of $n$-vertex instances in $\mathcal D$ can be decided in time $O^*(T(n))$ by a randomized algorithm whose error on yes- and on no-instances is at most $e^{-cn}$, for some $c>0$ (an exact algorithm qualifies). Then there is an algorithm that runs in time
--   $$O^*\big(T(n)\big)$$
--   on every instance of $\mathcal D$ and, whenever the instance is colorable, outputs an explicit list coloring with probability at least $1-e^{-n}$.
--
--   This is what allows the paper to state every algorithm as a decision algorithm; it is used inside Lemma 4.1 to turn the assumed $(k-1)$-list-coloring algorithm into one that finds colorings.
--
--   **Formalization Note** Algorithms and $O^*$ are as in the definition `Algorithms`: one program and two polynomials in the input bit size, fixed before the input; time is worst case over coin strings.
--
--   Differences from the source:
--   - generalization: a fixed palette $P$ → any class of instances closed under singleton restriction; reason: the instances over $P$ form such a class, and the source's proof only queries singleton restrictions (p. 8, "preserves the palette, the maximum list size, all degree conditions, and every other promise")
--   - generalization: "can be decided in time $T(n)$" → decided with error at most $e^{-cn}$ on both sides for some $c>0$; reason: exact algorithms are the case of zero error, and §3 (p. 7) allows exponentially small error for all algorithms
--   - reading: a running time $T(n)$ → $T(n)\ge 1$; reason: a running time counts at least one step
--   - reading: "an explicit list coloring can be found" → output is a list coloring with probability at least $1-e^{-n}$; reason: the bound the proof prints (p. 8, error $e^{-n}/(1+\sum_v|L(v)|)$ per query plus a union bound)
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - encoding: palette $P$ → colors in $\mathbb N$; reason: any finite palette is numbered
--   - generalization: nonempty lists → lists may be empty; reason: instances with an empty list are not colorable and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 8, Lemma 3.1

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms

open Classical

namespace KColoringFaster.ListBootstrap

/-- Lemma 3.1 (Decision-to-search for List Coloring), p. 8. Let `Dom` be a class of list instances
closed under singleton restriction (replacing `L v` by `{c}` for some `c ∈ L v`); a fixed palette
`P` is the class of instances with all lists inside `P`. If list colorability on `Dom` is decided in
time `O*(T(n))` (randomized, error at most `e^{-c n}` on both sides, for some `c > 0`; an exact
algorithm is the case of no error), then there is an algorithm running in time `O*(T(n))` on every
instance of `Dom` that outputs a list coloring with probability at least `1 - e^{-n}` whenever the
instance is colorable. -/
theorem lemma_3_1 (Dom : ListInstance → Prop)
    (hDom : ∀ I, Dom I → ∀ v, ∀ c ∈ I.L v, Dom (restrictAt I v c))
    (T : ℕ → ℝ) (hT : ∀ n, 1 ≤ T n) (c : ℝ) (hc : 0 < c)
    (hdec : RandDecides encList ListInstance.n Dom ListColorable (fun I => T I.n)
      (expErr c) (expErr c)) :
    RandFinds encList ListInstance.n Dom IsColoringOutput (fun I => T I.n) (expErr 1) := by sorry

end KColoringFaster.ListBootstrap
