-- Prove2me | Theorems.Thm_LocalBreadth_theorem_1_5
-- name    : LocalBreadth.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:37.702141+00:00
-- url     : https://prove2.me/theorems/54183e1d-4b71-4513-b2aa-4ffae24f4ec3
-- title:
--   Theorem 1.5 — exact one-dimensional value and simultaneous optimality
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   Then:
--
--   1. for every $K\in\mathcal X$ and every $n\ge1$, $b_n^{\mathrm{comb}}(K)=b_n^{\mathrm{top}}(K)$, and we write $b_n(K)$ for the common value;
--   2. $b_n(K)\to b(K)$ as $n\to\infty$;
--   3. (upper bound) for every fresh generator that is eventually valid on $\mathcal X$ and every $K\in\mathcal X$, there is a full enumeration of $K$ on which $d_{\mathrm{banach}}(O,K)\le b(K)$;
--   4. (lower bound) there is one fresh, eventually valid generator such that for every $K\in\mathcal X$ and every full enumeration of $K$, its output set satisfies $d_{\mathrm{banach}}(O,K)\ge b(K)$;
--   5. consequently, $b(K)$ is exactly the optimal worst-case lower Banach density for the target $K$: it is the greatest $\alpha$ for which some fresh, eventually valid generator has $d_{\mathrm{banach}}(O,K)\ge\alpha$ on every full enumeration of $K$. These optima are attained simultaneously, by clause 4's one generator.
--
--   This is the paper's central one-dimensional result. It converts an infinite online problem into a static combinatorial and topological quantity.
--
--   Differences from the source:
--   - encoding: a generator producing $o_t$ after receiving $x_t$, for $t\ge1$ → a function `List ℤ → ℤ` of the inputs so far, with time 0-indexed; reason: the generator is deterministic and unrestricted (pp.1, 16), so its outputs are determined by the inputs; same runs
--   - generalization: global freshness $o_t\notin S_t\cup O_{t-1}$ for every $t$ (p.13) → `IsFresh X G`, required only on full enumerations of members of $\mathcal X$; reason: this weakens the hypothesis on the generator, so the upper bound covers every globally fresh generator as well; the adversary only ever plays inside languages of $\mathcal X$
--   - encoding: a countable rooted tree with no infinite path → the inductive type `ObsTree` with `ℕ`-indexed children; reason: same trees up to repeated subtrees, which do not change the path set
--   - encoding: $U\subseteq\mathcal H_K$ open in the subspace $\mathcal H_K$ → $U$ open in the space of all histories and contained in $\mathcal H_K$; reason: $\mathcal H_K$ is open and closed (p.27), so the two agree
--   - encoding: $b(K)=\lim_n b_n(K)$ → `b X K` is $\sup_{n\ge1}b_n(K)$, with the limit as clause 2; reason: the printed limit becomes a proved claim instead of a value that could default
--   - reading: "Consequently, $b(K)$ is exactly the optimal worst-case lower Banach density" → `IsGreatest` of the set of densities guaranteed at $K$ by a fresh, eventually valid generator; reason: the page's sentence states optimality in words; this is its direct reading
--   - reading: "adversarial enumeration" and "eventually valid" in the theorem's sentence, with freshness unstated → full enumerations, universal validity on $\mathcal X$, and `IsFresh`; reason: the conventions of p.13, under which Theorem 1.8 restates this result
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Theorem 1.5, p.7; model conventions, p.13

import Mathlib
import Definitions.Def_LocalBreadth_Generator
import Definitions.Def_LocalBreadth_dBanach
import Definitions.Def_LocalBreadth_bComb
import Definitions.Def_LocalBreadth_bTop

open Filter Topology

namespace LocalBreadth

/-- Theorem 1.5 (Exact one-dimensional value and simultaneous optimality). Kleinberg, Wei, STOC 2027
submission (manuscript sha256 f924cbfc…), p.7. For a nonempty countable family `X` of infinite subsets of `ℤ`:
`b_n^comb(K) = b_n^top(K)` for all `K ∈ X`, `n ≥ 1`; `b_n(K) → b(K)`; every fresh, eventually valid generator
has, for every `K ∈ X`, a full enumeration of `K` with `d_banach(O, K) ≤ b(K)`; one fresh, eventually valid
generator has `d_banach(O, K) ≥ b(K)` for every `K ∈ X` on every full enumeration of `K`; and consequently `b(K)`
is the greatest density guaranteed at `K` by any such generator.

**Formalization Note.** Freshness and full enumerations are the model conventions of p.13, which the theorem's
sentence leaves implicit. The two predicates apply to full enumerations of members of `X`. -/
theorem theorem_1_5 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) :
    (∀ K ∈ X, ∀ n : ℕ, 1 ≤ n → bComb X n K = bTop X n K) ∧
    (∀ K ∈ X, Tendsto (fun n : ℕ => bComb X n K) atTop (𝓝 (b X K))) ∧
    (∀ G : Generator, IsFresh X G → IsEventuallyValid X G →
      ∀ K ∈ X, ∃ x, IsFullEnumeration K x ∧ dBanach (outputSet G x) K ≤ b X K) ∧
    (∃ G : Generator, IsFresh X G ∧ IsEventuallyValid X G ∧
      ∀ K ∈ X, ∀ x, IsFullEnumeration K x → b X K ≤ dBanach (outputSet G x) K) ∧
    (∀ K ∈ X, IsGreatest {α : ℝ | ∃ G : Generator, IsFresh X G ∧ IsEventuallyValid X G ∧
      ∀ x, IsFullEnumeration K x → α ≤ dBanach (outputSet G x) K} (b X K)) := by sorry

end LocalBreadth
