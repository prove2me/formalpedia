-- Prove2me | Theorems.Thm_GelfandVNA_Duality_theorem_3_20
-- name    : GelfandVNA.Duality.theorem_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:27.561044+00:00
-- url     : https://prove2.me/theorems/72063463-7edd-4a19-b293-30d0adb31929
-- title:
--   Theorem 3.20, p. 28 — MLoc ≃ CVNA^op, with inverse ProjLoc
-- statement:
--   The functors $\mathsf{Step}\colon\mathsf{LBAlg}\to\mathsf{CVNA}$ and $\mathsf{ProjAlg}\colon\mathsf{CVNA}\to\mathsf{LBAlg}$ form an adjoint equivalence; equivalently
--   $$\mathsf{MLoc}=\mathsf{LBAlg}^{\mathrm{op}}\ \simeq\ \mathsf{CVNA}^{\mathrm{op}},$$
--   with inverse $\mathsf{ProjLoc}$. The statement asserts an equivalence $e$ whose inverse sends a commutative von Neumann algebra $A$ to a measurable locale order-isomorphic (by $\iota_A$) to $\mathsf{ProjAlg}(A)$, and sends a normal \*-homomorphism $f\colon A\to B$ to the restriction of $f$ to projections:
--   $$\iota_B\big(e^{-1}(f)^*\,p\big)=f\big(\iota_A(p)\big).$$
--
--   This is the third equivalence of Theorem 1.1 and the localic form of the duality between commutative von Neumann algebras and measure algebras.
--
--   **Formalization Note** The equivalence and the isomorphisms $\iota_A$ are existentially quantified; $L^\infty$ and $\mathsf{Step}$ are not named, since an equivalence determines its inverse up to isomorphism.
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 28, Theorem 3.20

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_VNA

namespace GelfandVNA.Duality

open CategoryTheory Opposite

universe u

/-- Theorem 3.20, p. 28: `Step ⊣ ProjAlg` is an adjoint equivalence `LBAlg ≃ CVNA`, hence
`MLoc ≃ CVNA^op` with inverse `ProjLoc`: it sends `A` to (an algebra order-isomorphic to)
`ProjAlg(A)`, and a normal *-homomorphism `f` to the restriction of `f` to projections. -/
theorem theorem_3_20 :
    ∃ e : MLoc.{u} ≌ CVNA.{u}ᵒᵖ,
      ∃ ι : ∀ A : CVNA.{u}, (e.inverse.obj (op A)).carrier ≃o ProjAlg A.carrier,
        ∀ {A B : CVNA.{u}} (f : A ⟶ B) (p : (e.inverse.obj (op A)).carrier),
          (ι B (MLoc.frameHom (e.inverse.map f.op) p)).val = f.1 (ι A p).val := by sorry

end GelfandVNA.Duality
