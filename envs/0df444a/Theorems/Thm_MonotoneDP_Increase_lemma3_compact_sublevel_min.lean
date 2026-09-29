-- Prove2me | Theorems.Thm_MonotoneDP_Increase_lemma3_compact_sublevel_min
-- name    : MonotoneDP.Increase.lemma3_compact_sublevel_min
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:01:01.605988+00:00
-- url     : https://prove2.me/theorems/d6a2b368-4a7e-4046-a7c4-6ba67d69f8b5
-- title:
--   Lemma 3 — a function with compact sublevel sets on U attains its minimum (Hausdorff C, nonempty U)
-- statement:
--   Let $C$ be a Hausdorff topological space, $f:C\to[-\infty,+\infty]$ a function and $U\subseteq C$ a nonempty set. Assume that for each $\lambda\in(-\infty,\infty)$ the sublevel set
--
--   $$U(\lambda)=\{u\in U\mid f(u)\le\lambda\}$$
--
--   is compact. Then $f$ attains a minimum over $U$: there is $u^*\in U$ with $f(u^*)\le f(u)$ for every $u\in U$.
--
--   No continuity of $f$ is assumed; compactness of the real sublevel sets replaces it. The minimum may be $-\infty$ or $+\infty$. The lemma is used in Proposition 12 to show that the infimum defining each value iterate is attained.
--
--   **Formalization Note** The page states the lemma for an arbitrary topological space $C$ and an arbitrary subset $U$. As printed it is false: on $\mathbb N$ with the cofinite topology every subset is compact, and $f(n)=-n$ has no minimum; for $U=\emptyset$ nothing attains. The paper's argument uses that nested nonempty compact sets have nonempty intersection, which holds in Hausdorff spaces. The Hausdorff property of $C$ and $U\ne\emptyset$ are therefore added.
-- source:
--   Bertsekas, Monotone Mappings with Application in Dynamic Programming, SIAM J. Control Optim. 15 (1977), p. 460 (PDF p. 23), Lemma 3 (and the definition of compactness preceding it). DOI 10.1137/0315031

import Mathlib

namespace MonotoneDP.Increase

/-- Bertsekas (1977), p. 460, Lemma 3, repaired: let `C` be a Hausdorff topological space,
`f : C → [−∞, +∞]` and `U ⊆ C` nonempty. If `U(λ) = {u ∈ U | f(u) ≤ λ}` is compact for each
`λ ∈ (−∞, ∞)`, then `f` attains a minimum over `U`. The page states it for an arbitrary topological
space and an arbitrary `U`; the Hausdorff property and `U ≠ ∅` are added (the printed statement is
false without them). -/
theorem lemma3_compact_sublevel_min {C : Type*} [TopologicalSpace C] [T2Space C]
    (f : C → EReal) (U : Set C) (hU : U.Nonempty)
    (hcpt : ∀ lam : ℝ, IsCompact {u ∈ U | f u ≤ (lam : EReal)}) :
    ∃ u ∈ U, IsMinOn f U u := by sorry

end MonotoneDP.Increase
