-- Prove2me | Theorems.Thm_OAI_PermanentBorder_KernelBilinear_mixed_coefficient_bound
-- name    : OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:34:07.039928+00:00
-- url     : https://prove2.me/theorems/e94063b4-64d5-4301-8b46-6f1de722cc47
-- title:
--   Binomial bound for the multihomogeneous Bézout number of the bilinear kernel system
-- statement:
--   Let $\kappa$ be a finite set with $m=|\kappa|$ elements and let $n\ge0$ be an integer. Take three blocks labelled $0,1,2$ with formal variables $T_0,T_1,T_2$, and a system of $(n+1)+n+m$ equations indexed by $\{0,\dots,n\}\sqcup\{0,\dots,n-1\}\sqcup\kappa$, where each equation of the first kind involves the blocks $0$ and $1$, each equation of the second kind the blocks $0$ and $2$, and each equation of the third kind the blocks $1$ and $2$. Its mixed polynomial, the product over all equations of $T_{\text{first block}}+T_{\text{second block}}$, is
--   $$P=(T_0+T_1)^{n+1}(T_0+T_2)^{n}(T_1+T_2)^{m}\in\mathbb{N}[T_0,T_1,T_2].$$
--   For the block dimensions $(m+1,n,n)$ its relevant coefficient satisfies
--
--   $$
--   \big[T_0^{m+1}T_1^{n}T_2^{n}\big]\,(T_0+T_1)^{n+1}(T_0+T_2)^{n}(T_1+T_2)^{m}\;\le\;2^{m}\binom{2n+1}{m+1}.
--   $$
--
--   The left-hand side is the multihomogeneous Bézout number of a square bilinear system on $\mathbb{P}^{m+1}\times\mathbb{P}^{n}\times\mathbb{P}^{n}$: the system expressing that $u$ is a right kernel vector and $w$ a left kernel vector of an $(n+1)\times(n+1)$ matrix pencil with $m+1$ parameters, together with $m$ polar equations $w^{\top}B_ku=0$. The inequality replaces this number by an explicit binomial expression, which becomes the bound on the number of simple polar points of a determinantal pencil (both sides are $0$ when $m>2n$).
--
--   **Formalization Note** The blocks are `Option Bool` (`none`, `some false`, `some true` play the roles of $0,1,2$), the equations are `Fin (n+1) ⊕ (Fin n ⊕ κ)`, the two block maps are `firstGroup` and `secondGroup`, the mixed polynomial is `Multigraded.mixedPolynomial firstGroup secondGroup` in `MvPolynomial Groups ℕ`, and the exponent vector is `dimensions κ n`, equal to $m+1$ at `none` and to $n$ at `some b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/KernelCharts.lean#L298-L314

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts

open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}

theorem OAI.PermanentBorder.KernelBilinear.mixed_coefficient_bound :
    (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
      (dimensions κ n) ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by sorry
