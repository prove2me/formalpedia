-- Prove2me | Theorems.Thm_ModularForm_mdifferentiable_alSlash
-- name    : ModularForm.mdifferentiable_alSlash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/9a72490d-a269-52d9-92c6-5b5b6b956b04
-- title:
--   Holomorphy of the Atkin–Lehner slash f∣_k W
-- statement:
--   Fix natural numbers $M$ and $q$ with $M \neq 0$, and let $W$ be an Atkin–Lehner datum at $(M,q)$, that is, the data of a natural number $R$ with $M = q R$ together with integers $a, b$ satisfying the Bézout relation $q a - R b = 1$. Let $k$ be an integer and let $f : \mathbb{H} \to \mathbb{C}$ be a function on the upper half-plane which is holomorphic, in the sense of being `MDifferentiable` for the trivial model with corners on $\mathbb{C}$ on both source and target (the upper half-plane carrying its standard complex manifold structure). The conclusion is that [`ModularForm.alSlash W k f`](def/ModularForm_AtkinLehnerDatum.html#L141), namely the weight-$k$ slash $f \mid[k] W.alGL$ of $f$ by the element $W.alGL$ of $\mathrm{GL}_2(\mathbb{R})$ obtained by mapping the integral matrix `W.mat` attached to the datum along $\mathbb{Z} \to \mathbb{R}$ (its determinant being nonzero, so that the matrix is indeed invertible), is again `MDifferentiable` for the same models with corners. Thus holomorphy on $\mathbb{H}$ is preserved by the Atkin–Lehner slash operator.
--
--   This is the holomorphy clause for the Atkin–Lehner operator $W_q$ in weight $k$: slashing by an invertible real $2\times 2$ matrix of positive determinant sends holomorphic functions on $\mathbb{H}$ to holomorphic functions. It serves as one of the defining conditions when the Atkin–Lehner slash is packaged as an operator on cusp forms, and is used in the analysis of $q$-expansion coefficients of primitive forms at primes dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_mdifferentiable_alSlash.lean

import Mathlib
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.mdifferentiable_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.alSlash W k f) := by sorry
