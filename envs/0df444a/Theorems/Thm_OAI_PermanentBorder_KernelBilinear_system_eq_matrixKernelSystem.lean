-- Prove2me | Theorems.Thm_OAI_PermanentBorder_KernelBilinear_system_eq_matrixKernelSystem
-- name    : OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:43:39.513044+00:00
-- url     : https://prove2.me/theorems/d31e4584-156a-4bdf-9884-1d64e4b51b6d
-- title:
--   In an affine chart, the bilinear kernel system of a matrix pencil coincides with the matrix kernel system
-- statement:
--   Fix $n\ge0$ and a finite set $\kappa$, and write $[n]=\{0,1,\dots,n\}$. Let $T$ be a complex normed space, $F:T\to\mathbb{C}^{[n]\times[n]}$ a matrix-valued map, $\psi:\mathbb{C}\times\mathbb{C}^{\kappa}\to T$ a map, and $h=(h_k)_{k\in\kappa}$ directions in $T$. Let $A_0$, $A_\star$, $A_k$ ($k\in\kappa$) and $B_k$ ($k\in\kappa$) be complex $[n]\times[n]$ matrices such that
--
--   - (pencil) $F(\psi(z))=A_0+z_\star A_\star+\sum_{k\in\kappa}z_kA_k$ for every $z=(z_\star,(z_k)_k)\in\mathbb{C}\times\mathbb{C}^{\kappa}$;
--   - (constant directional derivatives) $DF_{pq}(y)[h_k]=(B_k)_{pq}$ for all $y\in T$, all $k\in\kappa$ and all entries $p,q$.
--
--   *The bilinear kernel system.* Take three blocks of homogeneous variables, $(t,s_\star,(s_k)_{k\in\kappa})$, $u=(u_q)_{q\in[n]}$ and $w=(w_p)_{p\in[n]}$, and put $\mathcal L=tA_0+s_\star A_\star+\sum_ks_kA_k$. For a pivot column $i\in[n]$ the system $\Sigma_i$ consists of the polynomials
--   $$(\mathcal Lu)_p\ \ (p\in[n]),\qquad(w^{\top}\mathcal L)_q\ \ (q\in[n],\ q\neq i),\qquad w^{\top}B_ku\ \ (k\in\kappa),$$
--   that is, $n+1$ right-kernel equations, $n$ left-kernel equations and $|\kappa|$ polar equations.
--
--   *The chart.* For a pivot row $r\in[n]$ and $z=(z_1,(u',w'))$ with $z_1\in\mathbb{C}\times\mathbb{C}^{\kappa}$ and $u',w'\in\mathbb{C}^{n}$, let $\phi_{i,r}(z)$ be the point with $t=1$, $(s_\star,(s_k)_k)=z_1$, $u$ obtained by putting $1$ at position $i$ and the entries of $u'$ at the other positions in increasing order, and $w$ obtained in the same way from $1$ at position $r$ and $w'$. The values of $\Sigma_i$ are reordered by the linear isomorphism $\mathrm{out}_r$, which arranges them as $\big((\text{right eq. }r,\ (\text{polar eq. }k)_k),\ ((\text{right eq. }p)_{p\neq r},\ (\text{left eq. }q)_{q\neq i})\big)$.
--
--   *The matrix kernel system.* For a matrix function $G=\begin{pmatrix}g&\beta^{\top}\\ \gamma&E\end{pmatrix}$ on $T$ with rows and columns indexed by $\{\ast\}\sqcup\{0,\dots,n-1\}$, put $\hat u=(1,u')^{\top}$, $\hat w=(1,w')^{\top}$ and, with all blocks evaluated at $\psi(z_1)$,
--   $$\mathcal K_G(z)=\Big(\big(g+\beta^{\top}u',\ (\hat w^{\top}\,DG(\psi(z_1))[h_k]\,\hat u)_{k\in\kappa}\big),\ \big(\gamma+Eu',\ \beta^{\top}+w'^{\top}E\big)\Big),$$
--   where $DG(\cdot)[h_k]$ is the matrix of entrywise directional derivatives. Finally let $F^{(r,i)}$ be $F$ with its rows ordered as ($r$, then the others in increasing order) and its columns as ($i$, then the others).
--
--   Then for all $i,r\in[n]$ and all $z$,
--
--   $$
--   \mathrm{out}_r\Big(\big(P(\phi_{i,r}(z))\big)_{P\in\Sigma_i}\Big)=\mathcal K_{F^{(r,i)}}(z).
--   $$
--
--   The left side is algebraic: a square system of multihomogeneous polynomials on $\mathbb{P}^{|\kappa|+1}\times\mathbb{P}^{n}\times\mathbb{P}^{n}$, read in an affine chart. The right side is the analytic system whose simple zeros are obtained by lifting simple zeros of the polar system of $\det F$ (the determinant together with its directional derivatives). The identity allows a multihomogeneous Bézout bound for the polynomial system to count these analytic zeros.
--
--   **Formalization Note** The variables are `Variables κ n`, a sigma type over the blocks `Option Bool`; the first block is indexed by `Option (Option κ)`, with `none` the homogenising variable $t$. The pencil coefficients are indexed by `Option κ` (`none` is $\star$) and $z_1$ is converted by `optionProduct.symm`. The system is `system A₀ A B i`, the chart is `chart i r`, the reordering is `output r`, $\mathcal K_G$ is `matrixKernelSystem G ψ h`, and $F^{(r,i)}$ is `(F y).submatrix (pivotEquiv r) (pivotEquiv i)`. Directional derivatives are taken with `fderiv` on both sides, so the identity holds verbatim with Lean's convention for non-differentiable points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/BilinearCounts.lean#L176-L251

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts

open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {κ : Type} [Fintype κ] {n : ℕ}
variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T]

theorem OAI.PermanentBorder.KernelBilinear.system_eq_matrixKernelSystem
    (F : T → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (ψ : (ℂ × (κ → ℂ)) → T) (h : κ → T)
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : Option κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (B : κ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hlocal : ∀ z i j, A₀ i j + ∑ k, A k i j * optionProduct.symm z k = F (ψ z) i j)
    (hdir : ∀ y k i j, fderiv ℂ (fun y => F y i j) y (h k) = B k i j)
    (i r : Fin (n+1)) (z : ChartSpace κ n) :
    output r (fun j => eval (chart i r z) (system A₀ A B i j)) =
      matrixKernelSystem (fun y => (F y).submatrix (pivotEquiv r) (pivotEquiv i)) ψ h z := by sorry
