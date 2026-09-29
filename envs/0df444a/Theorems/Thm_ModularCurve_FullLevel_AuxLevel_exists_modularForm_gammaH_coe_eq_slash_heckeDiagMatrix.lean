-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix
-- name    : ModularCurve.FullLevel.AuxLevel.exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/9844580e-938d-5ed8-84cd-1463d4465464
-- title:
--   Stretching Γ(N)-forms by diag(N,1) to Γ_H(N²M')
-- statement:
--   Let $N$ and $M'$ be nonzero natural numbers with $\gcd(N,M')=1$, let $k$ be an integer, and let $F$ be a modular form of weight $k$ for the image in $\mathrm{GL}_2(\mathbb{R})$ of the principal congruence subgroup $\Gamma(N)\le \mathrm{SL}_2(\mathbb{Z})$. Write $D_N$ for [`ModularForm.heckeDiagMatrix N`](def/ModularForm_HeckeOperator.html#L21), the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper triangular matrix $\begin{pmatrix}N&0\\0&1\end{pmatrix}$. Then there exists a modular form $F'$ of the same weight $k$ for the group [`CohCarrier.GammaH (N ^ 2 * M') (levelH N M')`](def/CohCarrier_Level.html#L133), that is, the subgroup of those $\gamma\in\Gamma_0(N^2M')$ whose lower-right entry reduces, modulo $N^2M'$, into the kernel of $(\mathbb{Z}/N^2M')^\times\to(\mathbb{Z}/N)^\times$, viewed inside $\mathrm{GL}_2(\mathbb{R})$, such that three things hold: (i) as a function on the upper half-plane, $F' = F\mid_k D_N$; (ii) for every natural number $n$, the $n$-th coefficient of the period-$1$ $q$-expansion of $F'$ equals $N^{k-1}$ times the $n$-th coefficient of the period-$N$ $q$-expansion of $F$; and (iii) for every $\rho\in \mathrm{SL}_2(\mathbb{Z})$, writing $\rho=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ and `conjElemN N ρ` for the element $\begin{pmatrix}a&b/N\\Nc&d\end{pmatrix}=D_N^{-1}\rho D_N$ of $\mathrm{GL}_2(\mathbb{R})$, one has $F'\mid_k(D_N^{-1}\rho D_N)=(F\mid_k\rho)\mid_k D_N$.
--
--   This records the classical stretching operator $f\mapsto f(N\tau)$, which carries forms on $\Gamma(N)$ to forms on a group of $\Gamma_H$-type at level $N^2M'$, together with the resulting law for $q$-expansion coefficients and the conjugation rule governing its behaviour under $\mathrm{SL}_2(\mathbb{Z})$. It is used in the construction of the auxiliary weight-$4$ and weight-$3$ forms at full level, which are assembled from Eisenstein series on $\Gamma(N)$ evaluated at $N\tau$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.FullLevel.AuxLevel.exists_modularForm_gammaH_coe_eq_slash_heckeDiagMatrix
    (N : ℕ) [NeZero N] (M' : ℕ) [NeZero M'] (hNM' : Nat.Coprime N M') (k : ℤ)
    (F : ModularForm (CongruenceSubgroup.Gamma N : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ F' : ModularForm (CohCarrier.GammaH (N ^ 2 * M') (ModularCurve.FullLevel.levelH N M') :
            Subgroup (GL (Fin 2) ℝ)) k,
      (⇑F' : UpperHalfPlane → ℂ) = (⇑F : UpperHalfPlane → ℂ) ∣[k] (ModularForm.heckeDiagMatrix N : GL (Fin 2) ℝ) ∧
      (∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑F')).coeff n = (N : ℂ) ^ (k - 1) * (UpperHalfPlane.qExpansion (N : ℝ) (⇑F)).coeff n) ∧
      (∀ ρ : SL(2, ℤ),
        ((⇑F' : UpperHalfPlane → ℂ) ∣[k] ModularCurve.FullLevel.conjElemN N ρ) =
          (((⇑F : UpperHalfPlane → ℂ) ∣[k] (ρ : GL (Fin 2) ℝ)) ∣[k] (ModularForm.heckeDiagMatrix N : GL (Fin 2) ℝ))) := by sorry
