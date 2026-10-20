-- Prove2me | Theorems.Thm_Hintz2026_main_neg
-- name    : Hintz2026.main_neg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:17.986982+00:00
-- url     : https://prove2.me/theorems/dfeb2984-1ec0-43c8-9e49-6d30b21bd508
-- title:
--   Main theorem (negative spin): (1)$^-$ ⟺ (7) at each point of $U$ for $C^\infty$ fields
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The negative-spin system (1)$^-$ is obtained from (1a)–(1d) by Hintz's replacement rules $\psi_1\to-\psi_{-1}$, $\psi_2\to\psi_{-2}$, $k\to-n$, $s\to\ell$, $\mathcal L_{-1}^\dagger\to\mathcal L_{-1}$, $\mathcal L_2\to\mathcal L_2^\dagger$, $(\mathcal D_0+\tfrac{3}{\bar\rho^*})\to\Delta(\mathcal D_{-1}^\dagger+\tfrac{3}{\bar\rho^*})$, $\Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\to(\mathcal D_0-\tfrac{3}{\bar\rho^*})$; its residuals are `res1aN`…`res1dN` and `Sys1NegAt` is their conjunction at a point. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`). System (7) for the transformed variables $z_+=\operatorname{adj}(X)\,y_+$ and $z_-=X^*y_-$ (with $X$ the matrix integrating factor of eq. (5) and $\operatorname{adj}X=\det X\cdot X^{-1}$ since $\det X=Q^2-M^2$ is constant) is
--
--   $$D^-z_+=C^{(\varsigma)}z_-,\qquad D^+z_-=\operatorname{adj}(C^{(\varsigma)})\,z_+,\qquad C^{(\varsigma)}=\det X\cdot X^{-1}(c^{(\varsigma)}I-B^{(\varsigma)})(X^*)^{-1};$$
--
--   `Sys7At` is this pair of equations at a point.
--
--   **Statement.** Let $\omega,m\in\mathbb R$ and let $G=(\psi_{-2},\psi_{-1},n,\ell)$ be $C^\infty$ on $U$ (`NegSmooth`). Then for every $x\in U$,
--
--   $$\mathrm{Sys1NegAt}(\omega,m,G,x)\iff\mathrm{Sys7At}\bigl(-1,\omega,m,\,y_+^{(-)},y_-^{(-)},\,x\bigr),$$
--
--   with $z_+=\operatorname{adj}(X)\,y_+^{(-)}$, $z_-=X^*y_-^{(-)}$; the map is explicit and invertible on $U$ (`invNeg`). The two spins are the instances $\varsigma=\pm1$ of the same (4)⟺(7) step.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d) with the negative-spin replacement rules, (3), (4), (7); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.main_neg (p : SubextremalKN) (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x := by sorry
