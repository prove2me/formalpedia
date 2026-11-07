-- Prove2me | Theorems.Thm_LocalBreadth_one_mega_step
-- name    : LocalBreadth.one_mega_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:14.372642+00:00
-- url     : https://prove2.me/theorems/197771f1-5177-48e9-970b-fd5ef38421f2
-- title:
--   §4.1, eq. (11) — one mega step produces a permanently sparse interval
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   Let $G$ be a fresh generator, eventually valid on $\mathcal X$. Fix $K\in\mathcal X$, a positive integer $n$, a number $\varepsilon>0$, and an admissible obstruction tree $T$ rooted at $K$. Suppose that finitely many rounds have occurred, with all inputs so far in $K$. Fix a radius $R_0$ and a point $y\in K$.
--
--   Then the adversary can extend the inputs inside $K$, including $y$, to produce a root-to-leaf path $H$ of $T$ and a relative interval $J$ of $K$ such that $|J|\ge n$, $J\cap[-R_0,R_0]=\emptyset$, every point of $J$ has been used by one of the two players, and
--   $$\frac{|O\cap J|}{|J|}\le p(H,J)\le c_n(H)+\varepsilon.$$
--
--   Repeating this step at growing scales gives the upper bound of the main theorem.
--
--   Differences from the source:
--   - encoding: a generator producing $o_t$ after receiving $x_t$, for $t\ge1$ → a function `List ℤ → ℤ` of the inputs so far, with time 0-indexed; reason: the generator is deterministic and unrestricted (pp.1, 16), so its outputs are determined by the inputs; same runs
--   - generalization: global freshness $o_t\notin S_t\cup O_{t-1}$ for every $t$ (p.13) → `IsFresh X G`, required only on full enumerations of members of $\mathcal X$; reason: this weakens the hypothesis on the generator, so the upper bound covers every globally fresh generator as well; the adversary only ever plays inside languages of $\mathcal X$
--   - generalization: the refill reveals the first unused point of $K$ in a fixed ordering → an arbitrary prescribed point $y\in K$ is among the new inputs; reason: the first unused point is one such $y$, so the statement specializes to the page
--   - reading: $O$, the eventual output set, in (11) → the outputs on prefixes of the finite input list `xs'`; reason: the page's sealing paragraph: every point of $J$ is used, so by freshness no later round adds an output to $J$
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), §4.1, eq. (11), p.19; sealing, p.21; refill, pp.19, 22

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_cScore
import Definitions.Def_LocalBreadth_ObsTree

namespace LocalBreadth

/-- One mega step, §4.1, eq. (11), p.19, sealed on p.21. Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…). Against a fresh, eventually valid generator, after a finite input list `xs` inside
`K`, a `T`-mega step extends the inputs inside `K` and produces a root-to-leaf path `p` of `T` and a
relative interval `J` of `K`, beyond the region `[−R₀, R₀]`, with `|J| ≥ n`, every point of `J` used by a
player, and `|O ∩ J|/|J| ≤ p(H, J) ≤ c_n(H) + ε`.

**Formalization Note.** `O` on the page is the eventual output set; here it is the outputs on prefixes
of `xs'`, and "every point of `J` is used" plus freshness make the two equal. `y` is the point the
refill reveals (p.19, p.22); it ends up among the inputs. -/
theorem one_mega_step (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (G : Generator) (hfresh : IsFresh X G) (hvalid : IsEventuallyValid X G)
    (K : Set ℤ) (hK : K ∈ X) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (T : ObsTree) (hT : T.Admissible X) (hroot : T.label = K)
    (xs : List ℤ) (hxs : ∀ y ∈ xs, y ∈ K) (R₀ : ℕ) (y : ℤ) (hy : y ∈ K) :
    ∃ xs' : List ℤ, xs <+: xs' ∧ (∀ w ∈ xs', w ∈ K) ∧ y ∈ xs' ∧
      ∃ p ∈ T.paths, ∃ a c : ℤ,
        let J : Set ℤ := K ∩ Set.Icc a c
        let O : Set ℤ := {w | ∃ i < xs'.length, G (xs'.take (i + 1)) = w}
        n ≤ J.ncard ∧ Disjoint J (Set.Icc (-(R₀ : ℤ)) (R₀ : ℤ)) ∧
        (∀ w ∈ J, w ∈ xs' ∨ w ∈ O) ∧
        ((O ∩ J).ncard : ℝ) / (J.ncard : ℝ) ≤ pScore p J ∧
        pScore p J ≤ cScore n p + ε := by sorry

end LocalBreadth
