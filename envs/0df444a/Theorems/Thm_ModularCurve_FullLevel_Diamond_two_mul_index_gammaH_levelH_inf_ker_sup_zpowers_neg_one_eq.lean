-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
-- name    : ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/c394f63c-fd47-5daf-83dd-3d76e608cf5b
-- title:
--   Index of ±Γ_H(q²M') in SL₂(ℤ)
-- statement:
--   Let $q$ be a prime and $\ell_g$ a prime with $\ell_g \ge 3$, and let $M'$ be a nonzero natural number with $q \nmid M'$ and $\ell_g \mid M'$. Put $N = q^2 M'$ and let $H \le (\mathbb{Z}/N)^\times$ be the intersection of `levelH q M'`, the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, with the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/\ell_g)^\times$ coming from $\ell_g \mid M' \mid q^2M'$. Let $\Gamma =$ [`CohCarrier.GammaH N H`](def/CohCarrier_Level.html#L133) be the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ sending $\gamma$ to the class of its lower right entry. The assertion is the equality of natural numbers
--   $$2\,\bigl[\mathrm{SL}_2(\mathbb{Z}) : \Gamma \vee \langle -1\rangle\bigr] = q\,(q^2-1)\,(\ell_g-1)\,\psi(M'),$$
--   where $\langle -1 \rangle$ is the subgroup of integer powers of $-1 \in \mathrm{SL}_2(\mathbb{Z})$, the index is the index of the join (i.e. of $\pm\Gamma$), and $\psi(M') = \sum_{d \mid M',\ d \text{ squarefree}} M'/d$ is Dedekind's $\psi$. Subtractions are truncated subtraction of naturals.
--
--   This is the classical index computation for the congruence subgroup $\Gamma(q) \cap \Gamma_1(\ell_g) \cap \Gamma_0(M')$ cut out by the character group $H$, in the form $2[\mathrm{SL}_2(\mathbb{Z}):\pm\Gamma_H] = [\mathrm{SL}_2(\mathbb{Z}):\Gamma_H]$, the doubling being legitimate because $-1 \notin \Gamma_H$ here. It supplies the numerical input to the dimension count [`ModularCurve.FullLevel.Diamond.finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
    (q : ℕ) [Fact q.Prime] (ℓg : ℕ) [Fact ℓg.Prime] (hℓg3 : 3 ≤ ℓg)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (hℓgM' : ℓg ∣ M') :
    2 * (CohCarrier.GammaH (q ^ 2 * M')
          (levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) ⊔
        Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      q * (q ^ 2 - 1) * (ℓg - 1) * dedekindPsi M' := by sorry
