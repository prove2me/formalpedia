-- Prove2me | Theorems.Thm_GraphonCheeger_Supplement_theorem_2_12
-- name    : GraphonCheeger.Supplement.theorem_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:24:08.775912+00:00
-- url     : https://prove2.me/theorems/dcbdf676-a286-495b-a6e9-570d11455138
-- title:
--   Theorem 2.12 — $\widehat{\mathcal W}_\kappa$ is the set of coloured graphons modulo $\cong$, also on $[0,1]$ and pure
-- statement:
--   Let $\kappa\ge1$. The map
--   $$
--   [W]\longmapsto\tau(W)=\bigl(t(F,W)\bigr)_F
--   $$
--   from the set of all $\kappa$-coloured graphons modulo the equivalence $\cong$ of Definition 2.6 to the set $\widehat{\mathcal W}_\kappa$ of $\kappa$-coloured graph limits is a bijection. It remains a bijection onto $\widehat{\mathcal W}_\kappa$ when restricted to the classes of pure coloured graphons defined on $[0,1]$.
--
--   Thus coloured graph limits may be regarded as equivalence classes of coloured graphons, and every class contains a pure coloured graphon on $[0,1]$.
--
--   **Formalization Note** The coloured graphons are bundled with their probability spaces `Ω : Type` (`AnyKGraphon κ`), and the quotient by $\cong$ is `GraphonClass κ`; `Set.BijOn` asserts that the map is defined on the whole quotient (respectively on the classes of `pureUnit` graphons), lands in $\widehat{\mathcal W}_\kappa$, is injective and is onto.
--
--   Differences from the source:
--   - reading: "can be identified with the set of all κ-coloured graphons modulo ≅" → the map [W] ↦ τ(W) is a bijection from the quotient onto Ŵκ, and stays one on the classes of pure coloured graphons on [0, 1]; reason: the identification is the map W ↦ Ŵ of Theorem 2.11 (proof of Theorem 2.12, p.10)
--   - encoding: all κ-coloured graphons (on all probability spaces) → graphons on probability spaces Ω : Type, bundled in AnyKGraphon κ; reason: all graphons form a proper class; one universe containing [0, 1] and every Fin n suffices
--   - encoding: test graphs F ∈ U (unlabelled coloured graphs); limits as points of [0,1]^U → labelled coloured graphs on Fin (n+1) (LIdx κ); points of ℝ^L with the product topology; reason: t(F, ·) is invariant under relabelling (p.8), so equalities, convergence and limits over L and U agree; ℝ^L only changes the ambient space
--   - encoding: W₁ ≅ W₂ (Definition 2.6: one, and thus all, of the conditions of Lemma 2.5) → CEquiv: t(F, W₁) = t(F, W₂) for every coloured graph F; reason: condition (i) of Lemma 2.5, which Definition 2.6 lists as equivalent to the others
--   - encoding: κ ≥ 1 (Definition 2.1) → [NeZero κ]; reason: the same condition
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Theorem 2.12, p.10 (PDF p.10)

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_GraphonClass

open MeasureTheory

namespace GraphonCheeger.Supplement

/-- Theorem 2.12, p.10 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): the set `Ŵ_κ` of `κ`-coloured graph limits can be identified with the
set of all `κ`-coloured graphons modulo the equivalence `≅` of Definition 2.6; furthermore, one
may restrict to coloured graphons defined on `[0, 1]`, and to pure coloured graphons, without
affecting the resulting space of graph limits.

**Formalization Note.**
* "Identified" is the map `[W] ↦ τ(W)` (`limitOf`) from the quotient `GraphonClass κ` of all
  coloured graphons (on probability spaces `Ω : Type`) by `≅` to `Ŵ_κ = GraphLimitSpace κ`
  (Def. 3.5 (W1)): it is a bijection (`Set.BijOn` on the whole quotient), and it stays a bijection
  onto `Ŵ_κ` on the classes of pure coloured graphons on `[0, 1]` (`pureUnit`). `κ ≥ 1` is
  `[NeZero κ]`. -/
theorem theorem_2_12 (κ : ℕ) [NeZero κ] :
    Set.BijOn (limitOf (κ := κ)) Set.univ (GraphLimitSpace κ) ∧
    Set.BijOn (limitOf (κ := κ))
      {c : GraphonClass κ | ∃ (W : unitInterval → unitInterval → ℝ) (hW : IsGraphon W)
        (χ : unitInterval → Fin κ) (hχ : Measurable χ),
        c = (Quotient.mk (graphonSetoid κ) (pureUnit W hW χ hχ) : GraphonClass κ)}
      (GraphLimitSpace κ) := by sorry

end GraphonCheeger.Supplement
