-- Prove2me | Theorems.Thm_ModularForm_alSlash_mul
-- name    : ModularForm.alSlash_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/1a4150b1-6e92-54b3-ac7d-ea3e9bf4ac6f
-- title:
--   The Atkin–Lehner slash is multiplicative up to a factor q
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum at $(M,q)$, i.e. a natural number $R$ together with the relation $M = qR$ and integers $a,b$ satisfying the Bézout identity $qa - Rb = 1$. Such a datum determines an integral $2\times 2$ matrix `W.mat`, whose image in $\mathrm{GL}_2(\mathbb{R})$ is `W.alGL` (the entries mapped along $\mathbb{Z} \to \mathbb{R}$; invertibility comes from its determinant being $q \neq 0$), and for a weight $k \in \mathbb{Z}$ the operator $\mathrm{alSlash}_W(k)$ is simply the Mathlib weight-$k$ slash action of `W.alGL`, namely $f \mapsto f \mid_k W.alGL$. The assertion is that for all integers $k_1, k_2$ and all functions $F, G : \mathbb{H} \to \mathbb{C}$ — no holomorphy, growth or invariance hypotheses whatsoever — one has $$\mathrm{alSlash}_W(k_1+k_2)(F\cdot G) \;=\; q \cdot \bigl(\mathrm{alSlash}_W(k_1)(F)\cdot \mathrm{alSlash}_W(k_2)(G)\bigr),$$ as an identity of functions $\mathbb{H} \to \mathbb{C}$, the scalar $q$ being the image of the natural number $q$ in $\mathbb{C}$ and the products being pointwise.
--
--   This records the failure of strict multiplicativity of the Atkin–Lehner slash operator $W_q$ under the normalisation $f\mid_k\gamma = |\det\gamma|^{k-1} f(\gamma\tau)(c\tau+d)^{-k}$ used in Mathlib: splitting a weight into $k_1+k_2$ introduces one extra factor of $|\det W.alGL| = q$ (with the classical $|\det|^{k/2}$ normalisation the constant would be $1$). It is used in the study of $q$-expansion coefficients of cusp forms with integral Atkin–Lehner slash, where a form is factored as a product (for instance against a power of $\Delta$) and the factor $q$ must be carried along.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_mul.lean

import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularForm.alSlash_mul {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (k₁ k₂ : ℤ) (F G : ℍ → ℂ) : ModularForm.alSlash W (k₁ + k₂) (F * G) = (q : ℂ) • (ModularForm.alSlash W k₁ F * ModularForm.alSlash W k₂ G) := by sorry
