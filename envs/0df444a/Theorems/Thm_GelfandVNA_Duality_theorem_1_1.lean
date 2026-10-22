-- Prove2me | Theorems.Thm_GelfandVNA_Duality_theorem_1_1
-- name    : GelfandVNA.Duality.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:26.137646+00:00
-- url     : https://prove2.me/theorems/e8111648-92b8-40b9-86f3-b013fd428926
-- title:
--   Theorem 1.1, p. 2 — CSLEMS, HStonean, HStoneanLoc, MLoc and CVNA^op are equivalent categories
-- statement:
--   The following five categories are equivalent:
--
--   1. **CSLEMS**: compact strictly localizable enhanced measurable spaces $(X,M,N)$ (a set, a σ-algebra, a σ-ideal of negligible sets), with morphisms the premaps $f$ (defined on a conegligible subset, with $f^*M'\subseteq M$ and $f^*N'\subseteq N$) modulo weak equality almost everywhere: $f\approx g$ iff $f^*m\oplus g^*m\in N$ for all $m\in M'$;
--   2. **HStonean**: hyperstonean spaces and open continuous maps;
--   3. **HStoneanLoc**: hyperstonean locales and open maps;
--   4. **MLoc**: measurable locales, the full subcategory of locales on the complete Boolean algebras with sufficiently many continuous valuations;
--   5. **CVNA$^{\mathrm{op}}$**: the opposite of commutative von Neumann algebras and normal \*-homomorphisms.
--
--   The equivalences are those of the diagram on p. 3:
--   $$\mathsf{HStonean}\simeq\mathsf{HStoneanLoc}\simeq\mathsf{MLoc},\qquad\mathsf{CSLEMS}\simeq\mathsf{MLoc},\qquad\mathsf{MLoc}\simeq\mathsf{CVNA}^{\mathrm{op}}.$$
--
--   This is a Gelfand-type duality for commutative von Neumann algebras: the measure-theoretic analogue of the duality between compact Hausdorff spaces and commutative unital C\*-algebras.
--
--   **Formalization Note** The statement is the four equivalences of the p. 3 diagram, each as `Nonempty (_ ≌ _)`, all at one universe. Mathlib's `≌` is an adjoint equivalence. The morphisms of CSLEMS are partial premaps, as Definition 4.6 requires. The bullet of Theorem 1.1 says "maps of sets $f\colon X\to X'$", but with total maps the theorem fails: $(\mathrm{pt},2^{\mathrm{pt}},2^{\mathrm{pt}})$ is in CSLEMS with $M/N=0$ and has no total map to $\varnothing$ (Remarks 4.9, 4.15).
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, pp. 2–3, Theorem 1.1

import Mathlib
import Definitions.Def_GelfandVNA_Duality_Locales
import Definitions.Def_GelfandVNA_Duality_Spaces
import Definitions.Def_GelfandVNA_Duality_VNA
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Theorem 1.1, p. 2: the categories `CSLEMS`, `HStonean`, `HStoneanLoc`, `MLoc` and `CVNA^op`
are equivalent, through the four equivalences of the diagram on p. 3. -/
theorem theorem_1_1 :
    Nonempty (HStonean.{u} ≌ HStoneanLoc.{u}) ∧ Nonempty (HStoneanLoc.{u} ≌ MLoc.{u}) ∧
      Nonempty (CSLEMS.{u} ≌ MLoc.{u}) ∧ Nonempty (MLoc.{u} ≌ CVNA.{u}ᵒᵖ) := by sorry

end GelfandVNA.Duality
