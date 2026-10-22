-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_4_65
-- name    : GelfandVNA.Duality.proposition_4_65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:47.34759+00:00
-- url     : https://prove2.me/theorems/b3ef130d-5ad9-4b7b-8123-c4d626bbbcc5
-- title:
--   Proposition 4.65, p. 39 — a morphism into a strictly localizable space has a measurable image, unique mod N′
-- statement:
--   Let $(X,M,N)$ be a compact enhanced measurable space that admits a faithful semifinite measure, let $(X',M',N')$ be strictly localizable, and let $f\colon(X,M,N)\to(X',M',N')$ be a premap. Then $f$ has a **measurable image**: there is $m\in M'$ with
--   $$f^*(X'\setminus m)\in N\quad\text{and}\quad\big(m'\in M',\ m'\subseteq m,\ f^*m'\in N\big)\ \Longrightarrow\ m'\in N'.$$
--   Moreover the class of $m$ in $M'/N'$ is unique: any two measurable images have symmetric difference in $N'$.
--
--   The measurable image is used to reduce Lemma 5.11 (suprema are preserved by $\mathsf{ML}(f)$) to an injective map.
--
--   **Formalization Note** The page prints $f^*(X\setminus m)$; since $m\subseteq X'$ the complement is taken in $X'$, as in the proof and in Lemma 5.11 ($f^*(X'\setminus X'_1)\in N$). "Faithful semifinite measure" is Definition 4.28: a complex measure on an ideal $M'\subseteq M$ that is faithful and semifinite, whose restrictions $\mu|_m$ ($m\in M'$) are countably additive with absolutely convergent sums (Remark 4.29; see the definitions module).
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 39, Proposition 4.65

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Proposition 4.65, p. 39: a premap `f` from a compact enhanced measurable space with a faithful
semifinite measure to a strictly localizable one has a measurable image `m ∈ M'`
(`f* (X' \ m) ∈ N`, and `m' ⊂ m`, `f* m' ∈ N` imply `m' ∈ N'`), unique modulo `N'`. -/
theorem proposition_4_65 {X X' : Type u} (E : Enhanced X) (E' : Enhanced X')
    (hc : IsCompactEnhancedOn E Set.univ)
    (hμ : ∃ (M' : Set (Set X)) (μ : Set X → ℂ),
      IsEMeasure E M' μ ∧ IsFaithfulEMeasure E M' μ ∧ IsSemifiniteEMeasure E M')
    (hsl : IsStrictlyLocalizable E') (f : Premap E E') :
    (∃ m : Set X', IsMeasurableImage E E' f m) ∧
    ∀ m₀ m₁ : Set X', IsMeasurableImage E E' f m₀ → IsMeasurableImage E E' f m₁ →
      (m₀ \ m₁) ∪ (m₁ \ m₀) ∈ E'.negligible := by sorry

end GelfandVNA.Duality
