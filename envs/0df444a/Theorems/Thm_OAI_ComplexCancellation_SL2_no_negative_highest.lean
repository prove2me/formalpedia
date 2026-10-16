-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_SL2_no_negative_highest
-- name    : OAI.ComplexCancellation.SL2.no_negative_highest
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:48:47.851991+00:00
-- url     : https://prove2.me/theorems/1bf8aa65-ee87-4528-b3f8-24152c7326ef
-- title:
--   A highest-weight vector of negative weight with nilpotent lowering orbit vanishes
-- statement:
--   Let $V$ be a complex vector space and let $\delta,\eta,H:V\to V$ be $\mathbb{C}$-linear maps satisfying the two commutation relations
--
--   $$
--   \delta\eta-\eta\delta=H,\qquad H\eta=\eta H-2\eta ,
--   $$
--
--   so that $\delta$ plays the role of a raising operator, $\eta$ of a lowering operator and $H=[\delta,\eta]$ of the weight operator of $\mathfrak{sl}_2$ (the third relation $[H,\delta]=2\delta$ is not assumed).
--
--   **Theorem.** Let $r\in V$ and let $w\in\mathbb{Z}$ with $w<0$. Suppose that $r$ is a highest-weight vector of weight $w$ on which the lowering operator is nilpotent:
--
--   $$
--   \delta(r)=0,\qquad H(r)=w\,r,\qquad \eta^{n}(r)=0\ \text{ for some } n\in\mathbb{N}.
--   $$
--
--   Then $r=0$.
--
--   This is the familiar fact from the representation theory of $\mathfrak{sl}_2$ that highest weights are nonnegative, in a form that needs no finite-dimensionality: only the two relations above and nilpotence of $\eta$ on the single vector $r$ are used. It therefore applies to infinite-dimensional spaces such as coordinate rings on which $\delta$, $\eta$, $H$ act by derivations, where it shows that an element killed by the raising derivation and lying in a locally nilpotent orbit of the lowering derivation cannot have negative weight.
--
--   **Formalization Note** The space $V$ is any type `R` with `[AddCommGroup R] [Module ℂ R]`, and $\delta,\eta,H$ are `R →ₗ[ℂ] R`. The weight $w$ is an integer cast to $\mathbb{C}$, and $\eta^n(r)$ is the iterate `(η : R → R)^[n] r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/HighestWeight.lean#L10-L60

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation

open OAI OAI.ComplexCancellation
variable {R : Type*} [AddCommGroup R] [Module ℂ R]

theorem OAI.ComplexCancellation.SL2.no_negative_highest (δ η H : R →ₗ[ℂ] R)
    (hcomm : ∀ r, δ (η r) - η (δ r) = H r)
    (hlower : ∀ r, H (η r) = η (H r) - (2 : ℂ) • η r)
    (r : R) (w : ℤ) (hw : w < 0) (hδ : δ r = 0)
    (hH : H r = (w : ℂ) • r) (hη : ∃ n : ℕ, (η : R → R)^[n] r = 0) : r = 0 := by sorry
