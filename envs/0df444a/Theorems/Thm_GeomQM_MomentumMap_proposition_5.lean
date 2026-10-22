-- Prove2me | Theorems.Thm_GeomQM_MomentumMap_proposition_5
-- name    : GeomQM.MomentumMap.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:38.582991+00:00
-- url     : https://prove2.me/theorems/b6d82757-c53f-46dd-ab8d-5fe677450359
-- title:
--   Proposition 5, p. 12 — the momentum map µ(ψ) = |ψ⟩⟨ψ| pulls Â, Λ and R back to f_A, the canonical bracket and G
-- statement:
--   Let $A,B$ be Hermitian $n\times n$ complex matrices and $\mu:\mathbb C^n\to\mathfrak u^*(\mathcal H)$, $\mu(\psi)=\rho_\psi=|\psi\rangle\langle\psi|$, the momentum map. On $\mathfrak u^*(\mathcal H)$ (Hermitian matrices $\xi$) let $\widehat A(\xi)=\tfrac12\operatorname{Tr}(\xi A)$, let $\Lambda$ be the Lie–Poisson tensor (11) and $\mathcal R$ the Jordan tensor (12):
--
--   $$\Lambda(d\widehat A,d\widehat B)(\xi)=\tfrac i2\operatorname{Tr}\,\xi\big(\alpha(A)\alpha(B)-\alpha(B)\alpha(A)\big),\qquad \mathcal R(\xi)(d\widehat A,d\widehat B)=\tfrac12\operatorname{Tr}\,\xi(AB+BA),$$
--
--   with $\alpha(A)=iA$. On $\mathbb C^n$ with coordinates $z_k=q_k+ip_k$ let $f_A(\psi)=\tfrac12\langle\psi|A\psi\rangle$, let $\{\cdot,\cdot\}$ be the canonical Poisson bracket and $G$ the contravariant Euclidean structure $\sum_k(\partial_{q_k}\otimes\partial_{q_k}+\partial_{p_k}\otimes\partial_{p_k})$. Then for every $\psi\in\mathbb C^n$:
--
--   1. $\mu^*(\widehat A)=f_A$, i.e. $\widehat A(\mu(\psi))=f_A(\psi)$;
--   2. $\mu^*(\{\widehat A,\widehat B\})=\{f_A,f_B\}$, i.e.
--   $$\{f_A,f_B\}(\psi)=\Lambda(d\widehat A,d\widehat B)(\mu(\psi));$$
--   3. $\mu^*(\mathcal R(d\widehat A,d\widehat B))=G(\mu^*(d\widehat A),\mu^*(d\widehat B))$, i.e.
--   $$G(df_A,df_B)(\psi)=\mathcal R(\mu(\psi))(d\widehat A,d\widehat B).$$
--
--   The momentum map thus realizes the Lie and Jordan structures of the observables by the symplectic and Euclidean parts of the Kähler structure of $\mathbb C^n$, on quadratic functions; this is the paper's geometrization of the observables.
--
--   **Formalization Note** In bullets 2 and 3 the Hilbert-space side is written on the left. The brackets on $\mathbb C^n$ are computed from real Fréchet derivatives of $f_A$ along $e_k$ ($\partial/\partial q_k$) and $ie_k$ ($\partial/\partial p_k$); they are not defined algebraically. Bullet 3's right side $G(\mu^*d\widehat A,\mu^*d\widehat B)$ is written as $G(df_A,df_B)$, using bullet 1. Three conventions are pinned, each the one under which the printed statement holds: $\widehat A$ uses the pairing (4), $\tfrac12\operatorname{Tr}(\xi A)$, not (5); $\Lambda$ is (11) evaluated at $\alpha(A),\alpha(B)$; $\mathcal R$ is the right-most expression of (12). The real-valued functions take the real part of trace expressions that are real for Hermitian arguments. The second bracket $\{f_1,f_2\}_+$ displayed on p. 12 is not used: bullet 3 names $G$.
-- source:
--   Cariñena, Clemente-Gallardo & Marmo, Geometrization of Quantum Mechanics, arXiv:math-ph/0701053v2, p. 12, Proposition 5 (with eqs. (4), (11), (12) on pp. 4–6 and G on p. 11)

import Mathlib
import Definitions.Def_GeomQM_MomentumMap_Defs

namespace GeomQM.MomentumMap
open Matrix
theorem proposition_5 (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ψ : Fin n → ℂ) :
    linFn A (momentumMap ψ) = quadFn A ψ ∧
    poisson (quadFn A) (quadFn B) ψ = kks (momentumMap ψ) A B ∧
    metricG (quadFn A) (quadFn B) ψ = jordanTensor (momentumMap ψ) A B := by sorry
end GeomQM.MomentumMap
