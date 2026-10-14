-- Prove2me | Theorems.Thm_KunuguiNovikov_measurableSet_image_fst_of_isCompact_sections
-- name    : KunuguiNovikov.measurableSet_image_fst_of_isCompact_sections
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-10-11T16:44:44.223765+00:00
-- url     : https://prove2.me/theorems/54d7a43a-f5a7-4bb0-968a-701166b0b93d
-- title:
--   Novikov: the projection of a Borel set with compact sections is Borel
-- statement:
--   **Novikov's projection theorem for Borel sets with compact sections.** Let $X$ be a standard Borel space and let $Y$ be a separable metrizable space whose Borel $\sigma$-algebra is standard (for instance a Polish space, or a Borel subset of a Polish space with the relative topology). If $B \subseteq X \times Y$ is a Borel set such that every section
--   $$B_x = \{\, y \in Y : (x,y) \in B \,\}$$
--   is compact, then its projection
--   $$\pi_X(B) = \{\, x \in X : B_x \neq \emptyset \,\}$$
--   is a Borel subset of $X$.
--
--   In general the projection of a Borel set is only analytic; compactness of the sections is what makes it Borel. This is the projection half of the Kunugui–Novikov theorem used in Bäuerle–Rieder, Proposition 2.4.11, to show that $T_n v$ is measurable, and (applied to $B \cap (X \times F)$ for closed $F$) it yields measurable selectors of compact-valued correspondences.
--
--   **Formalization note.** Kechris states the theorem for Polish $Y$. The version here, for separable metrizable $Y$ with standard Borel $\sigma$-algebra, follows from it: such a $Y$ is a Borel subset of its completion $\widehat Y$ (Lusin–Souslin), so $B$ is Borel in $X \times \widehat Y$, and its sections stay compact in $\widehat Y$.
-- source:
--   A. S. Kechris, Classical Descriptive Set Theory, GTM 156, Springer 1995, Theorem 28.8 (Novikov); used in Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Springer 2011, proof of Proposition 2.4.11, p. 33

import Mathlib

namespace KunuguiNovikov

/-- Novikov's projection theorem for Borel sets with compact sections (Kechris, *Classical
Descriptive Set Theory*, Theorem 28.8; Bertsekas–Shreve / Bäuerle–Rieder cite it as the
Kunugui–Novikov theorem): if `X` is a standard Borel space, `Y` is a separable metrizable space
whose Borel σ-algebra is standard, and `B ⊆ X × Y` is a Borel set every section
`B_x = {y | (x, y) ∈ B}` of which is compact, then the projection `π_X(B)` is Borel. -/
theorem measurableSet_image_fst_of_isCompact_sections {X Y : Type*}
    [MeasurableSpace X] [StandardBorelSpace X]
    [TopologicalSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] [StandardBorelSpace Y]
    (B : Set (X × Y)) (hB : MeasurableSet B) (hc : ∀ x, IsCompact {y | (x, y) ∈ B}) :
    MeasurableSet (Prod.fst '' B) := by sorry

end KunuguiNovikov
