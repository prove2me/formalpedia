-- Prove2me | Theorems.Thm_OAI_Problem346_derivation_eq_zero_of_positive_weight
-- name    : OAI.Problem346.derivation_eq_zero_of_positive_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:39:25.152877+00:00
-- url     : https://prove2.me/theorems/1f2d432a-b66f-4931-900a-9a29ab148393
-- title:
--   Polynomials of positive weight killed by the lowering derivation of an $\mathfrak{sl}_2$-triple of derivations vanish
-- statement:
--   Let $K$ be a field of characteristic zero, $\sigma$ an arbitrary (possibly infinite) set of variables, and $K[X]=K[X_i : i\in\sigma]$ the polynomial ring. Let $D,E,H$ be $K$-linear derivations of $K[X]$ such that
--
--   $$
--   [E,D]=H,\qquad [H,E]=2E,\qquad E\bigl(E(X_i)\bigr)=0\ \text{ for every } i\in\sigma,
--   $$
--
--   where $[A,B]=A\circ B-B\circ A$ is the commutator of derivations.
--
--   **Theorem.** Let $f\in K[X]$ and $p,q\in\mathbb{N}$ with $q<p$. If $H f=(p-q)\,f$ and $D f=0$, then $f=0$.
--
--   This is the polynomial form of positive-weight injectivity. It applies to polarization operators that move degree between two blocks of variables: $D=\sum_jY_j\,\partial/\partial X_j$, its reverse $E=\sum_jX_j\,\partial/\partial Y_j$, and $H$ the difference of the degree operators in the $X$-block and the $Y$-block. For these, $E^2$ kills every variable. The theorem then says that $D$ is injective on polynomials of degree $p$ in the $X$-variables and degree $q<p$ in the $Y$-variables, whatever the other variables. In the vanishing argument it is applied in exactly this form.
--
--   **Formalization Note** The derivations are `Derivation K (MvPolynomial σ K) (MvPolynomial σ K)`, and $[E,D]$ is the Lie bracket `⁅E, D⁆` of derivations. The weight is written $(p:K)-(q:K)$, the difference of the images of $p$ and $q$ in $K$. No finiteness assumption is placed on $\sigma$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/DerivationInjectivity.lean#L14-L38

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
open MvPolynomial
variable {K σ : Type*} [Field K] [CharZero K]

theorem OAI.Problem346.derivation_eq_zero_of_positive_weight
    (D E H : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (hED : ⁅E, D⁆ = H) (hHE : ⁅H, E⁆ = (2 : K) • E)
    (hEX : ∀ i : σ, E (E (X i)) = 0)
    (f : MvPolynomial σ K) (p q : ℕ) (hpq : q < p)
    (hf : H f = ((p : K) - q) • f) (hDf : D f = 0) : f = 0 := by sorry
