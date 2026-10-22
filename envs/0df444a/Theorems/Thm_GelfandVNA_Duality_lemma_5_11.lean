-- Prove2me | Theorems.Thm_GelfandVNA_Duality_lemma_5_11
-- name    : GelfandVNA.Duality.lemma_5_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:20.876607+00:00
-- url     : https://prove2.me/theorems/e446cff5-9d52-4d67-8f96-f99eb7d8e6c9
-- title:
--   Lemma 5.11 (Def 5.10), p. 42 — ML : CSLEMS → MLoc is well defined: f* : M′/N′ → M/N is a frame map
-- statement:
--   Let $f\colon(X,M,N)\to(X',M',N')$ be a morphism of compact strictly localizable enhanced measurable spaces (a class of premaps modulo weak equality almost everywhere). The induced map
--   $$f^*\colon M'/N'\to M/N,\qquad [m]\mapsto[f^*m],$$
--   preserves binary meets, the top element and **all existing suprema**. Hence $\mathsf{ML}(f)$ is a morphism of measurable locales, and $\mathsf{ML}\colon\mathsf{CSLEMS}\to\mathsf{MLoc}$, the restriction of $\mathsf{WeakML}$, is well defined (its value on objects is localizable by Proposition 4.54).
--
--   Compactness of the source is necessary: Remark 5.12 gives a morphism between a σ-finite and a strictly localizable space whose $f^*$ does not preserve suprema.
--
--   **Formalization Note** The map is `pullHom` of the EMS module applied to the underlying EMS morphism of $f$.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 42, Definition 5.10, Lemma 5.11

import Mathlib
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Lemma 5.11 with Definition 5.10, p. 42: `ML : CSLEMS → MLoc` is well defined on morphisms: for a
morphism `f` of compact strictly localizable enhanced measurable spaces, the induced map
`f* : M'/N' → M/N` preserves binary meets, the top element and all existing suprema, i.e. it is a
map of frames. -/
theorem lemma_5_11 {A B : CSLEMS.{u}} (f : A ⟶ B) :
    (∀ a b c : MmodN B.obj.E, IsGLB {a, b} c →
      IsGLB {pullHom f.hom a, pullHom f.hom b} (pullHom f.hom c)) ∧
    (∀ a : MmodN B.obj.E, IsGreatest Set.univ a → IsGreatest Set.univ (pullHom f.hom a)) ∧
    ∀ (s : Set (MmodN B.obj.E)) (a : MmodN B.obj.E), IsLUB s a →
      IsLUB (pullHom f.hom '' s) (pullHom f.hom a) := by sorry

end GelfandVNA.Duality
