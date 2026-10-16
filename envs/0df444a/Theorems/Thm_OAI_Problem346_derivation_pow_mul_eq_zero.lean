-- Prove2me | Theorems.Thm_OAI_Problem346_derivation_pow_mul_eq_zero
-- name    : OAI.Problem346.derivation_pow_mul_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:38:21.829895+00:00
-- url     : https://prove2.me/theorems/30ee02c9-5a2b-4fd7-92ca-58c0576b2839
-- title:
--   If $D^m a=0$ and $D^n b=0$ for a derivation $D$, then $D^{m+n}(ab)=0$
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra, and $D\colon A\to A$ an $R$-linear derivation, so that $D(ab)=a\,D(b)+b\,D(a)$ for all $a,b\in A$. For $k\in\mathbb{N}$ write $D^k$ for the $k$-fold composite of $D$, with $D^0=\mathrm{id}$.
--
--   **Theorem.** Let $m,n\in\mathbb{N}$ and $a,b\in A$ with $D^m a=0$ and $D^n b=0$. Then
--
--   $$
--   D^{m+n}(ab)=0 .
--   $$
--
--   Thus the set of elements on which $D$ is locally nilpotent (killed by some power of $D$) is closed under multiplication. Together with the obvious closure under addition, this shows that a derivation of a polynomial ring is locally nilpotent as soon as it is locally nilpotent on the variables. The exponent $m+n$ is not optimal (the general Leibniz formula gives $m+n-1$ when $m,n\ge1$), but it can be proved without binomial coefficients.
--
--   **Formalization Note** $D$ is a `Derivation R A A`, and $D^k$ is `D.toLinearMap ^ k`, the power in the ring of linear endomorphisms of $A$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/ShiftNilpotence.lean#L13-L46

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial

open OAI OAI.Problem346
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem OAI.Problem346.derivation_pow_mul_eq_zero (D : Derivation R A A)
    (m n : ℕ) (a b : A)
    (ha : (D.toLinearMap ^ m) a = 0)
    (hb : (D.toLinearMap ^ n) b = 0) :
    (D.toLinearMap ^ (m + n)) (a * b) = 0 := by sorry
