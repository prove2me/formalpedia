-- Prove2me | Theorems.Thm_Hintz2026_main
-- name    : Hintz2026.main
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-19T15:52:53.161981+00:00
-- url     : https://prove2.me/theorems/32cac5b9-2658-49bd-9396-6c1c1a7ded6e
-- title:
--   Atlas III goal: local equivalence of the Kerr–Newman perturbation systems (1) and (7), both spins
-- statement:
--   Fix subextremal Kerr–Newman parameters $M>0$, $Q\neq 0$, $a^2+Q^2<M^2$, a frequency $\omega\in\mathbb R$ and an azimuthal number $m$ (kept real), and let $U=\{r>r_+,\ 0<\theta<\pi\}$. The statement is the conjunction of the two spin cases.
--
--   **Positive spin.** For every quadruple of $C^\infty$ fields $(\psi_2,\psi_1,k,s)$ on $U$ and every $x\in U$: the four first-order equations (1a)–(1d) of Hintz hold at $x$ if and only if the transformed system (7),
--   $$(\sqrt\Delta\,\partial_r-i\partial_\theta)z_+=C\,z_-,\qquad(\sqrt\Delta\,\partial_r+i\partial_\theta)z_-=\operatorname{adj}(C)\,z_+,$$
--   holds at $x$ for $z_+=\operatorname{adj}(X)\,y_+^{(+)}$, $z_-=X^*\,y_-^{(+)}$, where $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,(\psi_2\pm i\Delta^{-1/2}\psi_1,\,-2Q(k\pm i\Delta^{-1/2}s))$ are the chiral variables of eq. (3), $X$ is the matrix integrating factor of eq. (5), and $C=\det X\cdot X^{-1}(c^{(+)}I-B^{(+)})(X^*)^{-1}$ with the coefficients of eq. (4).
--
--   **Negative spin.** The same equivalence for $C^\infty$ fields $(\psi_{-2},\psi_{-1},n,\ell)$, the negative-spin system obtained from (1a)–(1d) by the paper's replacement rules, the chiral variables $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\,2Q(n\mp i\Delta^{1/2}\ell))$ and the coefficients with $\varsigma=-1$.
--
--   The transformation $(\psi)\mapsto(y_+,y_-)\mapsto(z_+,z_-)$ is explicit and invertible on $U$ (inverse maps `invPos`, `invNeg`, `yplus_of_zplus`, `yminus_of_zminus`), so this is a two-sided local correspondence of solutions, proved for arbitrary $C^\infty$ fields rather than for known solutions. It is the algebraic core of Hintz's separation of variables; nothing is asserted about the angular eigenvalue problem, the radial reduction, boundary behaviour or mode stability.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2, eqs (1)-(7) (Steps 1-2); local source Atlas/Perturbations/Hintz2026/MainTheorem.lean (theorem main) (no public Git remote)

import Definitions.Def_Hintz2026_Chiral
open Hintz2026 Complex Function Matrix
open scoped ComplexConjugate ContDiff

theorem Hintz2026.main (p : SubextremalKN) (om mm : ℝ) : (∀ F : PosFields, PosSmooth p F → ∀ x ∈ U p, (Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x)) ∧ (∀ G : NegFields, NegSmooth p G → ∀ x ∈ U p, (Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x)) := by sorry
