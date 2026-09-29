-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq
-- name    : LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/faecbd2a-7146-570c-b58f-ded325fff762
-- title:
--   Whittaker functions agreeing on ι(GL₂) agree on ι(GL₂)N₃Z₃K₁
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F = \mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, so that `LocalGL3 p` is $GL_3(F)$. Let $W_1, W_2 \colon GL_3(F) \to \mathbb{C}$ be two functions which are Whittaker with respect to the inverse of the standard local additive character $\psi =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), in the sense of `IsGL3PsiWhittakerFn`: for all $x,y,z \in F$ and all $g$, $W_i(u(x,y,z)\,g) = \psi^{-1}(x+y)\,W_i(g)$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x, y$ above the diagonal and $z$ in the corner. Let $f \in \mathbb{N}$ and assume each $W_i$ is right invariant under the set `congruenceK1 (𝓞 ℚ) ℚ p f` of those $k \in GL_3(F)$ all of whose entries and all of whose entries of $k^{-1}$ have valuation $\le 1$ and which satisfy $v(k_{2,0}), v(k_{2,1}), v(k_{2,2}-1) \le \exp(-f)$; that is, $W_i(g k) = W_i(g)$ for all such $k$ and all $g$. Let $\omega \colon F^\times \to \mathbb{C}^\times$ be a group homomorphism and assume both $W_i$ transform by $\omega$ under the centre: $W_i(t I_3 \cdot h) = \omega(t) W_i(h)$ for all $t \in F^\times$ and all $h$. Finally assume $W_1$ and $W_2$ agree on the image of the embedding `iotaGL` of $GL_2(F)$ into $GL_3(F)$ as the block $\begin{pmatrix}h&0\\0&1\end{pmatrix}$. The conclusion is that for every $h \in GL_2(F)$, all $x,y,z \in F$, every $t \in F^\times$ and every $k$ in `congruenceK1 (𝓞 ℚ) ℚ p f`, one has $W_1(\iota(h)\,u(x,y,z)\,tI_3\,k) = W_2(\iota(h)\,u(x,y,z)\,tI_3\,k)$.
--
--   This is the uniqueness step saying that a $\psi^{-1}$-Whittaker function on $GL_3$ with given central character and right $K_1(p^f)$-invariance is determined on the product set $\iota(GL_2)\,N_3\,Z_3\,K_1(p^f)$ by its restriction to the embedded $GL_2$. It is used in the Rankin–Selberg computations of the Langlands–Tunnell part of the development, in the evaluation of the local integral over $\iota(GL_2)$ against a long Weyl element and a unipotent translate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors

open scoped Classical

theorem LanglandsTunnell.RankinSelberg.forall_apply_iotaGL_mul_upperUnipotent3_mul_scalar_mul_eq_of_forall_apply_iotaGL_eq
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W₁ W₂ : LocalGL3 p → ℂ)
    (hW₁ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₁)
    (hW₂ : IsGL3PsiWhittakerFn (NumberField.StandardAddChar.psiLocal ℚ p)⁻¹ W₂)
    (f : ℕ)
    (hK₁ : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₁ (g * k) = W₁ g)
    (hK₂ : ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ p f, ∀ g : LocalGL3 p, W₂ (g * k) = W₂ g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hω₁ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₁ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₁ h)
    (hω₂ : ∀ (t : (p.adicCompletion ℚ)ˣ) (h : LocalGL3 p),
      W₂ (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((ω t : ℂˣ) : ℂ) * W₂ h)
    (hι : ∀ h : GL (Fin 2) (p.adicCompletion ℚ), W₁ (iotaGL h) = W₂ (iotaGL h)) :
    ∀ (h : GL (Fin 2) (p.adicCompletion ℚ)) (x y z : p.adicCompletion ℚ) (t : (p.adicCompletion ℚ)ˣ) (k : LocalGL3 p),
      k ∈ congruenceK1 (𝓞 ℚ) ℚ p f →
        W₁ (iotaGL h * upperUnipotent3 x y z * Matrix.GeneralLinearGroup.scalar (Fin 3) t * k) =
          W₂ (iotaGL h * upperUnipotent3 x y z * Matrix.GeneralLinearGroup.scalar (Fin 3) t * k) := by sorry
