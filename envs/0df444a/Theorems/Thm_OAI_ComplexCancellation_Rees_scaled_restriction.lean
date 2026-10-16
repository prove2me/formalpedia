-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Rees_scaled_restriction
-- name    : OAI.ComplexCancellation.Rees.scaled_restriction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:55:32.45203+00:00
-- url     : https://prove2.me/theorems/78963261-085a-48fa-bf2f-9b7c3c7b5ebd
-- title:
--   From a locally nilpotent derivation of $A$ with invariant $r$ to one of $B$ killing $q$ and a numerator of $T^{i}r$
-- statement:
--   Let $P=\mathbb{C}[p,s,u,F,J]$, $x=s^2+u^3+p^2F$, $H=x^2F-(1+2sx)J-p^2J^2-pu$, and $A=P/(H)$. Let $L=A[T,T^{-1}]$ be the ring of Laurent polynomials over $A$, which contains $A$ as the constants. Let
--
--   $$
--   B=\mathbb{C}[q,\hat p,\hat s,\hat u,\hat F,\hat J]/(\hat H),\qquad \hat H=\hat x^2\hat F-(1+2\hat s\hat x)\hat J-\hat p^2\hat J^2-q^3\hat p\hat u,\qquad \hat x=\hat s^2+\hat u^3+\hat p^2\hat F .
--   $$
--
--   Let $\iota:B\to L$ be the $\mathbb{C}$-algebra homomorphism with
--
--   $$
--   q\mapsto T,\quad \hat p\mapsto pT^{-1},\quad \hat s\mapsto s,\quad \hat u\mapsto u,\quad \hat F\mapsto FT^2,\quad \hat J\mapsto JT^2
--   $$
--
--   (it is well defined because $\hat H\mapsto T^2H=0$, and it is injective).
--
--   **Theorem.** Let $D$ be a nonzero locally nilpotent $\mathbb{C}$-derivation of $A$ (for every $a\in A$ there is $n\in\mathbb{N}$ with $D^n(a)=0$), let $r\in A$ with $D(r)=0$, and let $i\in\mathbb{Z}$ and $b\in B$ satisfy $\iota(b)=T^i r$. Then there is a $\mathbb{C}$-derivation $E$ of $B$ such that
--
--   $$
--   E\ \text{is locally nilpotent},\qquad E\neq0,\qquad E(q)=0,\qquad E(b)=0 .
--   $$
--
--   Thus a nonzero locally nilpotent derivation of $A$ with an invariant $r$ is transported to the one-parameter family $B$, with both the parameter $q$ and the cleared numerator $b$ of $T^ir$ invariant. This is the first half of the passage from derivations of $A$ to derivations of the special fibre $B/qB$; the second half divides out powers of $q$ and reduces modulo $q$.
--
--   **Formalization Note** $B$ is `MvPolynomial (Fin 6) ℂ ⧸ (relation)` with `X 0, …, X 5` standing for $q,\hat p,\hat s,\hat u,\hat F,\hat J$; $A$ is `P ⧸ (H)` with `X 0, …, X 4` standing for $p,s,u,F,J$; $L$ is `LaurentPolynomial A` and $T^i$ is `T i`; $\iota$ is `Rees.embedding`; $r\in A$ enters $L$ through the constant embedding `c : A →ₐ[ℂ] L`, so the hypothesis reads `embedding s = T i * c r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/ReesDerivation.lean#L75-L96

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
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rees
open MvPolynomial LaurentPolynomial

theorem OAI.ComplexCancellation.Rees.scaled_restriction (D : Derivation ℂ A A) (hD : LND.LocallyNilpotent D)
    (hDn : D ≠ 0) (r : A) (hDr : D r=0) (i : ℤ) (s : B)
    (hs : embedding s=T i*c r) :
    ∃ E : Derivation ℂ B B, LND.LocallyNilpotent E ∧ E ≠ 0 ∧ E q=0 ∧ E s=0 := by sorry
