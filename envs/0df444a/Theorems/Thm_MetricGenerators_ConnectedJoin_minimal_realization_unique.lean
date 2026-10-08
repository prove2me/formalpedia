-- Prove2me | Theorems.Thm_MetricGenerators_ConnectedJoin_minimal_realization_unique
-- name    : MetricGenerators.ConnectedJoin.minimal_realization_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:49:13.830892+00:00
-- url     : https://prove2.me/theorems/3a6b807e-5afe-47de-aa28-e402bf61eb08
-- title:
--   §3.2, p. 391 — a tree metric has an inclusionwise minimal realization, unique up to isomorphism
-- statement:
--   Let $\mu$ be a tree metric on a set $X$. Then:
--
--   1. $\mu$ has an inclusionwise minimal realization $(A,g)$;
--   2. if $(A,g)$ and $(A',g')$ are two inclusionwise minimal realizations of $\mu$, there is a graph isomorphism $\psi:A\to A'$ with
--
--   $$\psi\bigl(g(x)\bigr)=g'(x)\qquad\text{for every }x\in X.$$
--
--   This is what makes "the" minimal realization $A$ of $\mu_G|_T$ and the set $T'=g(T)$ in Theorem 6 well defined; the paper stresses that the necessity half of Theorem 6 rests on it.
--
--   **Formalization Note.** "Unique up to isomorphism" is read as unique up to an isomorphism that maps $g(x)$ to $g'(x)$: Theorem 6's conditions refer to $T'=g(T)$, so an isomorphism ignoring the labels would not suffice, and the paper's construction of $A$ from the labelled points gives the labelled version. Realizations are trees on $\mathrm{Fin}\,N$.
-- source:
--   Sebő and Tannier, On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004), DOI 10.1287/moor.1030.0070, p. 391, §3.2 (unnumbered, in italics)

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

namespace MetricGenerators.ConnectedJoin

/-- **§3.2, p. 391 (unnumbered, in italics).** "If μ is a tree metric on a set X, there is a unique
(up to isomorphism) inclusionwise minimal tree A which is a realization of μ." (Sebő and Tannier,
On Metric Generators of Graphs, Math. Oper. Res. 29(2):383–393 (2004),
DOI 10.1287/moor.1030.0070, p. 391.)

If `μ` is a tree metric on `X`, then (a) `μ` has an inclusionwise minimal realization, and (b) any
two inclusionwise minimal realizations `(A, g)` and `(A', g')` are isomorphic by a graph
isomorphism `ψ : A ≃ A'` with `ψ (g x) = g' x` for every `x ∈ X`.

**Formalization Note.** "Unique up to isomorphism" is read as unique up to an isomorphism that
commutes with the realization maps: this is what Theorem 6 uses (its conditions refer to
`T′ = g(T)`), and it is what the paper's construction gives (it builds `A` from the labelled
points of `X`). Realizations are trees on `Fin N` (see `IsRealization`). -/
theorem minimal_realization_unique {X : Type*} (μ : X → X → ℕ) (hμ : IsTreeMetric μ) :
    (∃ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N), IsMinimalRealization μ A g) ∧
    ∀ (N : ℕ) (A : SimpleGraph (Fin N)) (g : X → Fin N)
      (N' : ℕ) (A' : SimpleGraph (Fin N')) (g' : X → Fin N'),
      IsMinimalRealization μ A g → IsMinimalRealization μ A' g' →
        ∃ ψ : A ≃g A', ∀ x : X, ψ (g x) = g' x := by sorry

end MetricGenerators.ConnectedJoin
