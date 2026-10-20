-- Prove2me | Theorems.Thm_Hintz2026_identN_m1
-- name    : Hintz2026.identN_m1
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:38.025989+00:00
-- url     : https://prove2.me/theorems/006d3e0b-5701-46bc-95e8-48a8fee777d6
-- title:
--   Chiralisation identity, negative spin: $D^-$ equation of (4), component 1
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. The negative-spin system (1)$^-$ is obtained from (1a)–(1d) by Hintz's replacement rules $\psi_1\to-\psi_{-1}$, $\psi_2\to\psi_{-2}$, $k\to-n$, $s\to\ell$, $\mathcal L_{-1}^\dagger\to\mathcal L_{-1}$, $\mathcal L_2\to\mathcal L_2^\dagger$, $(\mathcal D_0+\tfrac{3}{\bar\rho^*})\to\Delta(\mathcal D_{-1}^\dagger+\tfrac{3}{\bar\rho^*})$, $\Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\to(\mathcal D_0-\tfrac{3}{\bar\rho^*})$; its residuals are `res1aN`…`res1dN` and `Sys1NegAt` is their conjunction at a point. System (1) (positive spin, Hintz eqs (1a)–(1d)) for the four fields $(\psi_2,\psi_1,k,s)$ reads, with $\mathcal D_j=\partial_r+\tfrac{iK}{\Delta}+j\tfrac{\Delta'}{\Delta}$, $\mathcal L_j=\partial_\theta+\hat Q+j\cot\theta$, their daggers (sign of $iK/\Delta$, resp. $\hat Q$, flipped), $K=-(r^2+a^2)\omega+am$, $\hat Q=-a\omega\sin\theta+m/\sin\theta$, $F_\pm=3(M-Q^2/\bar\rho)\pm Q^2\bar\rho^*/\bar\rho^2$:
--
--   $$(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_2-(\mathcal D_0+\tfrac{3}{\bar\rho^*})\psi_1=-2kF_+,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})\psi_2+(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})\psi_1=2sF_-,$$
--
--   $$(\mathcal D_0+\tfrac{3}{\bar\rho^*})s-(\mathcal L_{-1}^\dagger+\tfrac{3ia\sin\theta}{\bar\rho^*})k=\tfrac{\bar\rho}{\bar\rho^{*2}}\psi_2,\qquad \Delta(\mathcal D_2^\dagger-\tfrac{3}{\bar\rho^*})k+(\mathcal L_2-\tfrac{3ia\sin\theta}{\bar\rho^*})s=\tfrac{2\bar\rho}{\bar\rho^{*2}}\psi_1.$$
--
--   In Lean the four equations are encoded as the vanishing of the residuals `res1a`, `res1b`, `res1c`, `res1d` (left side minus right side), and `Sys1PosAt` is their conjunction at a point. The chiral variables of eq. (3) are $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,\bigl(\psi_2\pm i\Delta^{-1/2}\psi_1,\ -2Q(k\pm i\Delta^{-1/2}s)\bigr)$ (`yPos p (±1) F`) and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,\bigl(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\ 2Q(n\mp i\Delta^{1/2}\ell)\bigr)$ (`yNeg p (±1) G`).
--
--   For any fields that are slice-differentiable at $x\in U$ (hypothesis `PosDiff`/`NegDiff`), component 1 of the $D^-$ equation of system (4) with $\varsigma=-1$, evaluated on the chiral variables, equals the prefactor times a fixed linear combination of the residuals of system (1):
--
--   $$\bigl[D^-y_+-A\,y_+-(c^{(-1)}I-B^{(-1)})\,y_-\bigr]_1=\Delta^{-3/4}\sqrt{\sin\theta}\cdot\bigl(2Q\,(-i\,\mathrm{res}_{1c}^--\sqrt{\Delta}\,\mathrm{res}_{1d}^-)\bigr)\quad\text{at }x.$$
--
--   This is one of the eight scalar identities that make the chiralisation (1)→(4) an identity for arbitrary fields, not only for solutions; the proof clears all denominators ($\bar\rho,\bar\rho^*,\Delta,\sqrt{\Delta},\sin\theta,Q$) and reduces powers of $\sqrt{\Delta}$, $\cos\theta$ and $i$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d) with the negative-spin replacement rules, (3), (4); local source Atlas/Perturbations/Hintz2026/Eq1to4Neg.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Matrix Function
open scoped ComplexConjugate ContDiff

theorem Hintz2026.identN_m1 (p : SubextremalKN) (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) : Dm p (fun z => yNeg p 1 G z 1) x - (A p x *ᵥ yNeg p 1 G x) 1 - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p (-1) om mm x) *ᵥ yNeg p (-1) G x) 1 = ↑(preNeg p x) * ((2 * ↑p.Q) * (-I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x)) := by sorry
