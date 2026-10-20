-- Prove2me | Theorems.Thm_Hintz2026_sys1_iff_sys4_neg
-- name    : Hintz2026.sys1_iff_sys4_neg
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:22.642993+00:00
-- url     : https://prove2.me/theorems/929eec57-4358-4edd-a88b-7b1c609524ec
-- title:
--   Local equivalence (1)$^-$ ⟺ (4), negative spin $\varsigma=-1$
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The negative-spin system (1)$^-$ is obtained from (1a)–(1d) by Hintz's replacement rules $\psi_1\to-\psi_{-1}$, $\psi_2\to\psi_{-2}$, $k\to-n$, $s\to\ell$, $\mathcal L_{-1}^\dagger\to\mathcal L_{-1}$, $\mathcal L_2\to\mathcal L_2^\dagger$, $(\mathcal D_0+\tfrac{3}{\bar\rho^*})\to\Delta(\mathcal D_{-1}^\dagger+\tfrac{3}{\bar\rho^*})$, $\Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\to(\mathcal D_0-\tfrac{3}{\bar\rho^*})$; its residuals are `res1aN`…`res1dN` and `Sys1NegAt` is their conjunction at a point. System (4) with spin parameter $\varsigma$ is
--
--   $$(\sqrt{\Delta}\partial_r\mp i\partial_\theta\mp A)\,y_\pm=(c^{(\varsigma)}I\mp B^{(\varsigma)})\,y_\mp,$$
--
--   with $A$, $B^{(\varsigma)}$, $c^{(\varsigma)}$ the explicit coefficient data of Hintz eq. (4) (`A`, `Bmat`, `cscalar`); `Sys4At` is the pair of these vector equations at a point. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`).
--
--   For fields $(\psi_{-2},\psi_{-1},n,\ell)$ slice-differentiable at $x\in U$ (`NegDiff`): the negative-spin system (1)$^-$ holds at $x$ if and only if system (4) with $\varsigma=-1$ holds at $x$ for $y_\pm=y_\pm^{(-)}$,
--
--   $$\mathrm{Sys1NegAt}(\omega,m,G,x)\iff\mathrm{Sys4At}(-1,\omega,m,\,y_+^{(-)},y_-^{(-)},\,x).$$
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d) with the negative-spin replacement rules, (3), (4); local source Atlas/Perturbations/Hintz2026/Equivalence1to4.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.sys1_iff_sys4_neg (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) : Sys1NegAt p om mm G x ↔ Sys4At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x := by sorry
