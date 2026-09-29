-- Prove2me | Theorems.Thm_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
-- name    : ModularForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e6169427-e504-51c7-b768-c82de727eb08
-- title:
--   Atkin–Lehner slash preserves level-Γ_H(M) modular forms
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for $(M,q)$, that is: a natural number $R$ together with the identity $M = qR$ and integers $a, b$ satisfying $qa - Rb = 1$; the datum carries an associated integral $2\times 2$ matrix `W.mat` of determinant $q$, viewed through `W.alGL` as an element of $GL_2(\mathbb{R})$. Let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ and assume that every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/q)^\times$ attached to the divisibility $q \mid M$ (witnessed by $M = qR$) equals $1$ lies in $H$. Let $k$ be an integer and let $f$ be a modular form of weight $k$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $SL(2,\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$ sending $\gamma$ to the reduction mod $M$ of its lower right entry (so: matrices in $\Gamma_0(M)$ with $d(\gamma) \bmod M \in H$), regarded as a subgroup of $GL_2(\mathbb{R})$. Then there is a modular form $X$ of weight $k$ for the same group whose underlying function $\mathbb{H} \to \mathbb{C}$ is [`ModularForm.alSlash W k f`](def/ModularForm_AtkinLehnerDatum.html#L141), the weight-$k$ slash $f \mid[k] W.alGL$ of $f$ by `W.alGL`.
--
--   This is the statement that the Atkin–Lehner involution at an exact divisor $q$ of $M$ acts on the space of modular forms of weight $k$ and level $\Gamma_H(M)$, under the hypothesis that $H$ contains the kernel of $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/q)^\times$; it is the non-cuspidal counterpart of the corresponding statement for cusp forms, and is used in the analysis of $q$-expansions of Atkin–Lehner translates of cusp forms at maximal ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one.lean

import Mathlib
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_AtkinLehnerDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_GammaH_coe_eq_alSlash_of_forall_unitsMap_atkinLehnerFactor_eq_one
    {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (H : Subgroup (ZMod M)ˣ)
    (hHq : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro W.R W.hM.symm) u = 1 → u ∈ H)
    (k : ℤ) (f : ModularForm (CohCarrier.GammaH M H) k) :
    ∃ X : ModularForm (CohCarrier.GammaH M H) k, ⇑X = ModularForm.alSlash W k ⇑f := by sorry
