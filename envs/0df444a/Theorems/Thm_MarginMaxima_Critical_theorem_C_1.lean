-- Prove2me | Theorems.Thm_MarginMaxima_Critical_theorem_C_1
-- name    : MarginMaxima.Critical.theorem_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:03:53.071924+00:00
-- url     : https://prove2.me/theorems/8948499e-374a-430a-9144-644cb0fba67a
-- title:
--   Theorem C.1 — entropy upper bound for every Lipschitz aggregation: $\mathrm{fat}_\gamma(\mathcal G)\le 82W(1+H(p))$
-- statement:
--   Let $G:\mathbb R^r\to\mathbb R$ be $L$-Lipschitz for $\|\cdot\|_\infty$, let $\rho_1,\dots,\rho_r>0$ and $\gamma>0$, and let $\mathcal G$ be the class $x\mapsto G(\langle u_1,x\rangle,\dots,\langle u_r,x\rangle)$ on the unit ball, $\|u_j\|\le\rho_j$. With $J=\{j:L\rho_j\ge\gamma\}$, $w_j=L^2\rho_j^2/\gamma^2$ ($j\in J$), $W=\sum_Jw_j$, $p_j=w_j/W$,
--   $$\mathrm{fat}_\gamma(\mathcal G)\le 82\,W\,(1+H(p)),$$
--   read as $0$ if $J=\emptyset$. For $R_j$-bounded affine functions $\langle u_j,x\rangle+b_j$, $\|u_j\|,|b_j|\le R_j$, the same holds with $\rho_j=2R_j$.
--
--   With $G=\max$, $L=1$, $\rho_j=1$ and $\gamma\le1$ it gives $\mathrm{fat}_\gamma(F_{\max,r})\le 82r(1+\ln r)/\gamma^2$, the upper bound of Theorem 1.1(a).
--
--   Differences from the source:
--   - encoding: G L-Lipschitz for ∥·∥∞ → L : ℝ≥0 and LipschitzWith L G on Fin r → ℝ; reason: Mathlib's metric on Fin r → ℝ is the sup metric; a Lipschitz constant is nonnegative
--   - encoding: the class on the unit ball (dimension not named) → the statement for every dimension d, on Ball d; reason: the paper notes the bound holds in each d (proof of Theorem 1.2, p. 33)
--   - encoding: fat_γ(𝒢) ≤ 82W(1 + H(p)), read as 0 if J = ∅ → (fat (LipClass d r G ρ) γ : ℝ≥0∞) ≤ ENNReal.ofReal (entropyBound L ρ γ), entropyBound = 0 when J = ∅; reason: fat is ℕ∞-valued, so an infinite fat is not hidden
--   - encoding: ρ_1, …, ρ_r > 0 and R_j-bounded affine functions with ρ_j = 2R_j → ∀ ρ with all ρ_j > 0, and ∀ R with all R_j > 0 using entropyBound L (2R) γ; reason: the affine clause needs ρ_j = 2R_j > 0 as in the first clause
-- source:
--   Tianlang Chen, The Margin Complexity of Maxima of Linear Functionals, STOC 2027 submission (manuscript sha256 dbfb896a…3901), p. 30, Theorem C.1

import Mathlib
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_MarginMaxima_Critical_MaxClass
import Definitions.Def_MarginMaxima_Critical_LipClass

open BartlettNN.Margin
open scoped ENNReal NNReal

namespace MarginMaxima.Critical

theorem theorem_C_1 (r : ℕ) (G : (Fin r → ℝ) → ℝ) (L : ℝ≥0) (hG : LipschitzWith L G)
    (γ : ℝ) (hγ : 0 < γ) (d : ℕ) :
    (∀ ρ : Fin r → ℝ, (∀ j, 0 < ρ j) →
      (fat (LipClass d r G ρ) γ : ℝ≥0∞) ≤ ENNReal.ofReal (entropyBound L ρ γ)) ∧
    (∀ R : Fin r → ℝ, (∀ j, 0 < R j) →
      (fat (AffLipClass d r G R) γ : ℝ≥0∞) ≤
        ENNReal.ofReal (entropyBound L (fun j => 2 * R j) γ)) := by sorry

end MarginMaxima.Critical
