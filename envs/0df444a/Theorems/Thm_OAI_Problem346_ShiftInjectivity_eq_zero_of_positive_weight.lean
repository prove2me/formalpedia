-- Prove2me | Theorems.Thm_OAI_Problem346_ShiftInjectivity_eq_zero_of_positive_weight
-- name    : OAI.Problem346.ShiftInjectivity.eq_zero_of_positive_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:34:23.152692+00:00
-- url     : https://prove2.me/theorems/0115f878-c5c2-491e-96ed-16965aff58f7
-- title:
--   Positive-weight vectors killed by the lowering operator of an $\mathfrak{sl}_2$-type triple vanish when the raising operator is nilpotent on them
-- statement:
--   Let $K$ be a field of characteristic zero and $M$ a vector space over $K$. Let $D,E,H\colon M\to M$ be $K$-linear maps such that, for every $z\in M$,
--
--   $$
--   D(Ez)=E(Dz)-Hz,\qquad H(Ez)=E(Hz)+2\,Ez .
--   $$
--
--   With commutators $[A,B]=AB-BA$ these relations say $[E,D]=H$ and $[H,E]=2E$. For $N\in\mathbb{N}$, $E^N$ is the $N$-fold composite of $E$, with $E^0=\mathrm{id}$.
--
--   **Theorem.** Let $x\in M$ and let $w$ be a positive integer such that $Hx=w\,x$, $Dx=0$, and $E^Nx=0$ for some $N\in\mathbb{N}$. Then $x=0$.
--
--   The relations are those of an $\mathfrak{sl}_2$-triple $(e,h,f)=(E,H,D)$, with $E$ raising and $D$ lowering the $H$-weight by $2$. The theorem says that a lowest-weight vector, one killed by $D$, cannot have positive weight if $E$ acts nilpotently on it. Equivalently, $D$ is injective on the space of $w$-eigenvectors of $H$ ($w>0$) on which $E$ acts nilpotently. No inner product, finite-dimensionality or other representation theory is required. Specialized to polarization derivations on polynomial rings, this gives the injectivity of degree-shifting operators used in the vanishing argument.
--
--   **Formalization Note** $D,E,H$ are elements of `Module.End K M`, the weight $w$ is a natural number cast into $K$, and $E^N$ is the power in the endomorphism ring.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/ShiftInjectivity.lean#L45-L66

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
variable {K M : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]

theorem OAI.Problem346.ShiftInjectivity.eq_zero_of_positive_weight (D E H : Module.End K M)
    (hDE : ∀ z, D (E z) = E (D z) - H z)
    (hHE : ∀ z, H (E z) = E (H z) + (2 : K) • E z)
    (x : M) (w : ℕ) (hw : 0 < w) (hx : H x = (w : K) • x)
    (hDx : D x = 0) (hnil : ∃ N : ℕ, (E ^ N) x = 0) : x = 0 := by sorry
