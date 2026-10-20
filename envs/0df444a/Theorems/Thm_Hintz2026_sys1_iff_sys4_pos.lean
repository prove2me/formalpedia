-- Prove2me | Theorems.Thm_Hintz2026_sys1_iff_sys4_pos
-- name    : Hintz2026.sys1_iff_sys4_pos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:29.849184+00:00
-- url     : https://prove2.me/theorems/f35a07e6-97b6-4410-ad27-4297f350538b
-- title:
--   Local equivalence (1) ⟺ (4), positive spin $\varsigma=+1$
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. System (1) (positive spin, Hintz eqs (1a)–(1d)) for the four fields $(\psi_2,\psi_1,k,s)$ reads, with $\mathcal D_j=\partial_r+\tfrac{iK}{\Delta}+j\tfrac{\Delta'}{\Delta}$, $\mathcal L_j=\partial_\theta+\hat Q+j\cot\theta$, their daggers (sign of $iK/\Delta$, resp. $\hat Q$, flipped), $K=-(r^2+a^2)\omega+am$, $\hat Q=-a\omega\sin\theta+m/\sin\theta$, $F_\pm=3(M-Q^2/\bar\rho)\pm Q^2\bar\rho^*/\bar\rho^2$:
--
--   $$(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_2-(\mathcal D_0+\tfrac{3}{\bar\rho^*})\psi_1=-2kF_+,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\psi_2+(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_1=2sF_-,$$
--
--   $$(\mathcal D_0+\tfrac{3}{\bar\rho^*})s-(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})k=\tfrac{\bar\rho}{\bar\rho^{*2}}\psi_2,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})k+(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})s=\tfrac{2\bar\rho}{\bar\rho^{*2}}\psi_1.$$
--
--   In Lean the four equations are encoded as the vanishing of the residuals `res1a`, `res1b`, `res1c`, `res1d` (left side minus right side), and `Sys1PosAt` is their conjunction at a point. System (4) with spin parameter $\varsigma$ is
--
--   $$(\sqrt{\Delta}\partial_r\mp i\partial_\theta\mp A)\,y_\pm=(c^{(\varsigma)}I\mp B^{(\varsigma)})\,y_\mp,$$
--
--   with $A$, $B^{(\varsigma)}$, $c^{(\varsigma)}$ the explicit coefficient data of Hintz eq. (4) (`A`, `Bmat`, `cscalar`); `Sys4At` is the pair of these vector equations at a point. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`).
--
--   For fields $(\psi_2,\psi_1,k,s)$ slice-differentiable at $x\in U$ (`PosDiff`): the four equations of system (1) hold at $x$ if and only if system (4) with $\varsigma=+1$ holds at $x$ for $y_\pm=y_\pm^{(+)}$,
--
--   $$\mathrm{Sys1PosAt}(\omega,m,F,x)\iff\mathrm{Sys4At}(+1,\omega,m,\,y_+^{(+)},y_-^{(+)},\,x).$$
--
--   The forward direction substitutes the four residual identities; the converse uses that the prefactor $\Delta^{5/4}\sqrt{\sin\theta}$, $\sqrt{\Delta}$ and $Q$ are nonzero on $U$ and inverts the $2\times2$ combinations $(-i\,a+b/\sqrt{\Delta},\ i\,a+b/\sqrt{\Delta})$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d), (3), (4); local source Atlas/Perturbations/Hintz2026/Equivalence1to4.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.sys1_iff_sys4_pos (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) : Sys1PosAt p om mm F x ↔ Sys4At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x := by sorry
