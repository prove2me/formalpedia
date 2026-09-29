-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq
-- name    : ModularCurve.FullLevel.dvd_of_redQ_smul_lineInfty_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/4b080589-0f07-5446-a8fd-2e0a12a43722
-- title:
--   Reduction fixing [1:0] forces q ∣ c
-- statement:
--   Let $q$ be a prime and let $\delta \in \mathrm{SL}_2(\mathbb{Z})$. Write $\mathrm{redQ}\,q$ for the group homomorphism $\mathrm{SL}_2(\mathbb{Z}) \to \mathrm{GL}_2(\mathbb{Z}/q)$ obtained by reducing the entries modulo $q$ (via the ring homomorphism $\mathbb{Z} \to \mathbb{Z}/q$) and then viewing the resulting special linear matrix as an element of the general linear group, and write $\mathrm{lineInfty}\,q$ for the point of the projectivization $\mathbb{P}((\mathbb{Z}/q)^2)$ represented by the vector $(1,0)$. The hypothesis is that the image $\mathrm{redQ}\,q\,\delta$ fixes this point under the natural action of $\mathrm{GL}_2(\mathbb{Z}/q)$ on the projectivization by matrix–(column-)vector multiplication, i.e. $\overline{\delta} \cdot [1:0] = [1:0]$. The conclusion is that $q$, viewed as an integer, divides the entry of the underlying integral matrix of $\delta$ in position $(1,0)$ — in the usual notation $\delta = \begin{pmatrix} a & b \\ c & d\end{pmatrix}$, that $q \mid c$.
--
--   This is the elementary statement that the stabiliser of the cusp $\infty = [1:0]$ in $\mathbb{P}^1(\mathbb{F}_q)$ is the reduction of the Borel, i.e. of the matrices with lower-left entry divisible by $q$. It is used as a step in the results on stability of the level structure at $\infty$, namely [`ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq) and its variants for $q = 2$ and $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_dvd_of_redQ_smul_lineInfty_eq.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.dvd_of_redQ_smul_lineInfty_eq
    (q : ℕ) [Fact q.Prime] (δ : SL(2, ℤ))
    (hfix : ModularCurve.FullLevel.redQ q δ • ModularCurve.FullLevel.lineInfty q = ModularCurve.FullLevel.lineInfty q) :
    (q : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by sorry
