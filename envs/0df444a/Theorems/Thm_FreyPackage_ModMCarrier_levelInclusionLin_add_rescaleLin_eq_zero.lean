-- Prove2me | Theorems.Thm_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero
-- name    : FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/95df5c1b-e644-5edd-89a4-bf15a8a30742
-- title:
--   Joint injectivity of the two degeneracy maps in weight 2
-- statement:
--   Let $R$, $M$, $q'$ be natural numbers with $M \neq 0$, let $q'$ be prime, suppose $q' \nmid R$, and suppose both $R \mid M$ and $q'R \mid M$. Let $x$ and $y$ be cusp forms of weight $2$ for $\Gamma_0(R)$ (in Mathlib's sense, for the image of $\Gamma_0(R) \le \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{GL}_2(\mathbb{R})$). Two $\mathbb{C}$-linear maps from weight-$2$ cusp forms of level $\Gamma_0(R)$ to weight-$2$ cusp forms of level $\Gamma_0(M)$ are in play: `levelInclusionLin hRM 2`, which sends a form to the very same function on the upper half-plane, its invariance and cuspidality at level $M$ following from $\Gamma_0(M) \le \Gamma_0(R)$ for $R \mid M$; and `rescaleLin hqRM 2`, which sends $y$ to $y \mid_2 \mathrm{diag}(q',1)$, the weight-$2$ slash of (the underlying function of) $y$ by `heckeDiagMatrix q'`, the matrix $\begin{pmatrix} q' & 0 \\ 0 & 1 \end{pmatrix}$ in $\mathrm{GL}_2(\mathbb{R})$. The assertion is that if the images add to zero, i.e. `levelInclusionLin hRM 2 x + rescaleLin hqRM 2 y = 0` in the space of weight-$2$ cusp forms for $\Gamma_0(M)$, then $x = 0$ and $y = 0$.
--
--   This is the weight-$2$ linear independence of the two families of oldforms coming from level $R$ inside level $M$ along the prime $q' \nmid R$, the input of Ihara-type arguments on the $q'$-old part; the coprimality hypothesis $q' \nmid R$ is essential, since for $q' \mid R$ the two images overlap. It is used in the computation of the determinant of the Hecke action at $q'$ on weight-$2$ cusp forms, in a rationality statement for $q$-expansion coefficients of traces, and in a vanishing criterion on the cohomological side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_ModMCarrier_levelInclusionLin_add_rescaleLin_eq_zero.lean

import Mathlib
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_FreyPackage_ModMCarrier_OldSublattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CongruenceSubgroup FreyPackage.ModMCarrier
open scoped ModularForm MatrixGroups

theorem FreyPackage.ModMCarrier.levelInclusionLin_add_rescaleLin_eq_zero
    {R M q' : ℕ} [NeZero M] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (hRM : R ∣ M) (hqRM : q' * R ∣ M)
    (x y : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (h : levelInclusionLin hRM 2 x + rescaleLin hqRM 2 y = 0) : x = 0 ∧ y = 0 := by sorry
