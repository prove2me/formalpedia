-- Prove2me | Theorems.Thm_OAI_Problem346_PolynomialShift_eq_zero_of_shift_eq_zero
-- name    : OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:41:01.98771+00:00
-- url     : https://prove2.me/theorems/349bb2c0-be84-46e9-9450-e0ec9f850453
-- title:
--   A block shift is injective when the source block degree exceeds the destination block degree
-- statement:
--   Let $B$ and $I$ be finite sets and let $\mathbb{C}[X]=\mathbb{C}[X_{b,i} : (b,i)\in B\times I]$ be the polynomial ring whose variables are grouped into *blocks* $\{X_{b,i} : i\in I\}$, one block for each $b\in B$. For a block $u\in B$ and $n\in\mathbb{N}$, a polynomial $f$ is *homogeneous of degree $n$ in block $u$* if every monomial occurring in $f$ with nonzero coefficient has total degree exactly $n$ in the variables $X_{u,i}$, $i\in I$ (the zero polynomial is homogeneous of every degree). For blocks $u,v\in B$, the *shift* $\Delta_{u\to v}$ is the $\mathbb{C}$-linear derivation of $\mathbb{C}[X]$ determined by $\Delta_{u\to v}(X_{b,i})=X_{v,i}$ if $b=u$ and $\Delta_{u\to v}(X_{b,i})=0$ otherwise; explicitly,
--
--   $$\Delta_{u\to v}=\sum_{i\in I}X_{v,i}\,\frac{\partial}{\partial X_{u,i}} .$$
--
--   **Theorem.** Let $\mathrm{src},\mathrm{dst}\in B$ be distinct blocks and let $p,q\in\mathbb{N}$ with $q<p$. Let $f\in\mathbb{C}[X]$ be homogeneous of degree $p$ in block $\mathrm{src}$ and homogeneous of degree $q$ in block $\mathrm{dst}$. Then
--
--   $$\Delta_{\mathrm{src}\to\mathrm{dst}}\,f=0\quad\Longrightarrow\quad f=0 .$$
--
--   Nothing is assumed about the degrees of $f$ in the remaining blocks: their variables are arbitrary spectators. In words, moving one unit of degree from a block of larger degree to a block of smaller degree is injective on the corresponding bi-homogeneous component. This is the polynomial form of the $\mathfrak{sl}_2$ principle that, when the raising operator acts locally nilpotently, a nonzero vector of strictly positive weight is never killed by the lowering operator. In the proof that the Foulkes–Howe map is surjective, it is the cancellation tool that undoes each derivative step of the transfer arguments.
--
--   **Formalization Note** $\Delta_{u\to v}$ is `PolynomialShift.shift u v`, the linear map underlying the derivation `PolynomialShift.derivation u v`. "Homogeneous of degree $n$ in block $u$" is `IsBlockHomogeneous u f n`, i.e. `MvPolynomial.IsWeightedHomogeneous` for the weight that is $1$ on the variables of block $u$ and $0$ on all other variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/BlockInjectivity.lean#L16-L40

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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift

open OAI OAI.Problem346 OAI.Problem346.PolynomialShift
open MvPolynomial PolynomialWeights
variable {B I : Type*} [Fintype B] [Fintype I] [DecidableEq B]

theorem OAI.Problem346.PolynomialShift.eq_zero_of_shift_eq_zero (src dst : B) (hsd : src ≠ dst)
    {f : MvPolynomial (B × I) ℂ} {p q : ℕ} (hpq : q < p)
    (hp : IsBlockHomogeneous src f p) (hq : IsBlockHomogeneous dst f q)
    (hDf : shift src dst f = 0) : f = 0 := by sorry
