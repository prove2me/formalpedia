-- Prove2me | Theorems.Thm_Hintz2026_main_pos
-- name    : Hintz2026.main_pos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:25.539751+00:00
-- url     : https://prove2.me/theorems/32df258e-18dc-45c1-9367-c301d9799ffb
-- title:
--   Main theorem (positive spin): (1) ⟺ (7) at each point of $U$ for $C^\infty$ fields
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. System (1) (positive spin, Hintz eqs (1a)–(1d)) for the four fields $(\psi_2,\psi_1,k,s)$ reads, with $\mathcal D_j=\partial_r+\tfrac{iK}{\Delta}+j\tfrac{\Delta'}{\Delta}$, $\mathcal L_j=\partial_\theta+\hat Q+j\cot\theta$, their daggers (sign of $iK/\Delta$, resp. $\hat Q$, flipped), $K=-(r^2+a^2)\omega+am$, $\hat Q=-a\omega\sin\theta+m/\sin\theta$, $F_\pm=3(M-Q^2/\bar\rho)\pm Q^2\bar\rho^*/\bar\rho^2$:
--
--   $$(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_2-(\mathcal D_0+\tfrac{3}{\bar\rho^*})\psi_1=-2kF_+,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\psi_2+(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_1=2sF_-,$$
--
--   $$(\mathcal D_0+\tfrac{3}{\bar\rho^*})s-(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})k=\tfrac{\bar\rho}{\bar\rho^{*2}}\psi_2,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})k+(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})s=\tfrac{2\bar\rho}{\bar\rho^{*2}}\psi_1.$$
--
--   In Lean the four equations are encoded as the vanishing of the residuals `res1a`, `res1b`, `res1c`, `res1d` (left side minus right side), and `Sys1PosAt` is their conjunction at a point. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). System (7) for the transformed variables $z_+=\operatorname{adj}(X)\,y_+$ and $z_-=X^*y_-$ (with $X$ the matrix integrating factor of eq. (5) and $\operatorname{adj}X=\det X\cdot X^{-1}$ since $\det X=Q^2-M^2$ is constant) is
--
--   $$D^-z_+=C^{(\varsigma)}z_-,\qquad D^+z_-=\operatorname{adj}(C^{(\varsigma)})\,z_+,\qquad C^{(\varsigma)}=\det X\cdot X^{-1}(c^{(\varsigma)}I-B^{(\varsigma)})(X^*)^{-1};$$
--
--   `Sys7At` is this pair of equations at a point.
--
--   **Statement.** Let $\omega,m\in\mathbb R$ and let $F=(\psi_2,\psi_1,k,s)$ be $C^\infty$ on $U$ (`PosSmooth`). Then for every $x\in U$,
--
--   $$\mathrm{Sys1PosAt}(\omega,m,F,x)\iff\mathrm{Sys7At}\bigl(+1,\omega,m,\,y_+^{(+)},y_-^{(+)},\,x\bigr),$$
--
--   i.e. the positive-spin system (1) holds at $x$ exactly when the transformed system (7) with $\varsigma=+1$ holds at $x$ for $z_+=\operatorname{adj}(X)\,y_+^{(+)}$, $z_-=X^*y_-^{(+)}$. The composite map $(\psi_2,\psi_1,k,s)\mapsto(y_+,y_-)\mapsto(z_+,z_-)$ is explicit and invertible on $U$ (`invPos`, `yPos_invPos`, `invPos_yPos`, and $y_+=(Q^2-M^2)^{-1}X z_+$, $y_-=(X^*)^{-1}z_-$). The proof chains the (1)⟺(4) equivalence with the (4)⟺(7) equivalence of the integrating-factor block. No spectral decomposition is asserted: (7) still has the matrix coupling $C$, which separates as $C=R(r)+i\Theta(\theta)$ (`Cmat_eq_Csep`).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d), (3), (4), (7); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.main_pos (p : SubextremalKN) (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x := by sorry
