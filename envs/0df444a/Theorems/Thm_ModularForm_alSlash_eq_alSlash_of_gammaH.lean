-- Prove2me | Theorems.Thm_ModularForm_alSlash_eq_alSlash_of_gammaH
-- name    : ModularForm.alSlash_eq_alSlash_of_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/a224fcaa-2037-5301-98d0-c81287ae1050
-- title:
--   Independence of the Atkin–Lehner slash on Γ_H(M)
-- statement:
--   Fix $M \ge 1$ (a natural number with a nonvanishing hypothesis), a natural number $q$, a subgroup $H \le (\mathbf Z/M)^\times$ and a weight $k \in \mathbf Z$. Let $W$ and $W'$ be two Atkin–Lehner data at $(M,q)$, i.e. two instances of the structure [`ModularForm.AtkinLehnerDatum M q`](def/ModularForm_AtkinLehnerDatum.html#L14), each consisting of a natural number $R$ with $M = qR$ together with integers $a,b$ satisfying the Bézout relation $qa - Rb = 1$; each such datum carries an associated integral $2 \times 2$ matrix [`ModularForm.AtkinLehnerDatum.mat`](def/ModularForm_AtkinLehnerDatum.html#L46) of nonzero determinant, whose entrywise image in $\mathbf R$ is regarded as an element `W.alGL` of $\mathrm{GL}_2(\mathbf R)$. Let $f$ be a cusp form of weight $k$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbf Z)$, namely the image in $\mathrm{SL}_2(\mathbf Z)$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbf Z/M)^\times$ sending $\gamma$ to the unit given by its lower right entry modulo $M$. Then the two weight-$k$ slashes agree as functions on the upper half plane: $f \mid_k W'.\mathrm{alGL} = f \mid_k W.\mathrm{alGL}$, i.e. `alSlash W' k f = alSlash W k f`.
--
--   The statement says that the Atkin–Lehner involution applied to a cusp form on $\Gamma_H(M)$ is independent of the choice of Bézout data defining the Atkin–Lehner matrix at $(M,q)$. It is used in [`ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash`](thm.html#ModularCurve.eq_zero_of_isInfReductionMap_apply_eq_zero_of_apply_eq_zero_alSlash), where a hypothesis imposed for a single datum is thereby available for all of them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_alSlash_eq_alSlash_of_gammaH.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularForm.alSlash_eq_alSlash_of_gammaH
    (M : ℕ) [NeZero M] (q : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    (W W' : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm.alSlash W' k (⇑f) = ModularForm.alSlash W k (⇑f) := by sorry
