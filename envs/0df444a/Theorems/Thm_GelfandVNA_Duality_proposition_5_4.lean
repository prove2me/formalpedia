-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_5_4
-- name    : GelfandVNA.Duality.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:16.711819+00:00
-- url     : https://prove2.me/theorems/503f75df-9496-426c-9d8d-092abad8ecf0
-- title:
--   Proposition 5.4, p. 40 — TM restricts to a functor HStonean → CSLEMS
-- statement:
--   For a topological space $S$ let $\mathrm{TM}(S)=(S,M,N)$, where $N$ is the σ-ideal of meager subsets and $M$ the σ-algebra of sets with the property of Baire (symmetric differences of an open and a meager set). The functor $\mathrm{TM}\colon\mathsf{TopOpen}\to\mathsf{EMS}$ restricts to a functor
--   $$\mathrm{TM}\colon\mathsf{HStonean}\to\mathsf{CSLEMS}.$$
--   Precisely: for every hyperstonean space $S$ the enhanced measurable space $\mathrm{TM}(S)$ is compact and strictly localizable, and every open continuous map $f\colon S\to T$ of hyperstonean spaces is a premap $\mathrm{TM}(S)\to\mathrm{TM}(T)$ (defined everywhere).
--
--   Together with Proposition 2.72 and 2.73 this defines $\mathrm{Spec}=\mathrm{TM}\circ\mathrm{Sp}\circ\mathrm{Ideal}\colon\mathsf{MLoc}\to\mathsf{CSLEMS}$.
--
--   **Formalization Note** The morphism clause holds for all open continuous maps (Lemma 5.3) and is included so that the statement covers "restricts to a functor".
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 40, Proposition 5.4 (with Definition 5.2, Lemma 5.3)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P20
import Definitions.Def_GelfandVNA_Duality_Spaces
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P20

universe u

/-- Proposition 5.4, p. 40: `TM : TopOpen → EMS` restricts to a functor `HStonean → CSLEMS`: for a
hyperstonean space `S`, `TM(S)` is compact and strictly localizable, and an open continuous map of
hyperstonean spaces is a premap `TM(S) → TM(T)` (with full point-set domain). -/
theorem proposition_5_4 :
    (∀ S : HStonean.{u}, IsCompactEnhancedOn (TM S.toTop) Set.univ ∧
      IsStrictlyLocalizable (TM S.toTop)) ∧
    ∀ {S T : HStonean.{u}} (f : S ⟶ T),
      IsPremap (TM S.toTop) (TM T.toTop) (fun x => some (f.1 x)) := by sorry

end GelfandVNA.Duality
