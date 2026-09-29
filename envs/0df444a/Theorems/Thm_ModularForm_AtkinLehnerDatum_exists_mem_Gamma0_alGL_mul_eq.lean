-- Prove2me | Theorems.Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq
-- name    : ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/95606a67-14d6-5d4a-a42a-cab353db646f
-- title:
--   The Atkin–Lehner matrix normalises Γ₀(M)
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum of level $M$ and index $q$, that is, a quadruple consisting of a natural number $R$ with $M = qR$ and integers $a, b$ satisfying the Bézout relation $qa - Rb = 1$. Write $W.\mathrm{alGL}$ for the element of $\mathrm{GL}_2(\mathbb{R})$ obtained from the integral matrix `W.mat` attached to the datum by applying the ring map $\mathbb{Z} \to \mathbb{R}$ entrywise; this is invertible because the determinant of `W.mat` is the positive integer $q$. Let $g \in \mathrm{SL}_2(\mathbb{Z})$ belong to the congruence subgroup $\Gamma_0(M)$, i.e. its lower-left entry is divisible by $M$. The assertion is that there exists $\delta \in \mathrm{SL}_2(\mathbb{Z})$, again lying in $\Gamma_0(M)$, such that the identity $W.\mathrm{alGL} \cdot \bar g = \bar\delta \cdot W.\mathrm{alGL}$ holds in $\mathrm{GL}_2(\mathbb{R})$, where $\bar{\,\cdot\,}$ denotes the homomorphism `Matrix.SpecialLinearGroup.mapGL ℝ` from $\mathrm{SL}_2(\mathbb{Z})$ to $\mathrm{GL}_2(\mathbb{R})$. In other words, conjugation by $W.\mathrm{alGL}$ carries the image of $\Gamma_0(M)$ into itself.
--
--   This is the normalisation property of the Atkin–Lehner matrix $W_q$ on $\Gamma_0(M)$ with $M = qR$, in the form of an explicit one-sided cocycle identity in $\mathrm{GL}_2(\mathbb{R})$. It is what makes the weight-$k$ slash action of $W_q$ preserve $\Gamma_0(M)$-invariance, and hence induce the Atkin–Lehner operator on modular and cusp forms of level $M$; it is used by the statements about `alSlash` of cusp forms, about its interaction with the diamond operators, and about $q$-expansions at the two cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_AtkinLehnerDatum_exists_mem_Gamma0_alGL_mul_eq.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.AtkinLehnerDatum.exists_mem_Gamma0_alGL_mul_eq {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by sorry
