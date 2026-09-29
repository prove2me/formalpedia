-- Prove2me | Theorems.Thm_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
-- name    : ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/afde4a9c-fa04-5c61-b1f2-8f9dadcfefde
-- title:
--   Mod p congruence between weights k+1 and k on Γ₁(p)
-- statement:
--   Let $p$ be a prime with $5 \le p$. The assertion is the existence of an integer $k$, a modular form $G$ of weight $k+1$ for the congruence subgroup $\Gamma_1(p)$, a modular form $H$ of weight $k$ for $\Gamma_1(p)$, and two integral power series $p_G, p_H \in \mathbb{Z}[[q]]$, such that: $p_G$ is an integral $q$-expansion of $G$ and $p_H$ is an integral $q$-expansion of $H$, in the sense that the image of each under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of the corresponding form taken with respect to width $1$ (parameter $q = e^{2\pi i \tau}$); the reduction of $p_H$ modulo $p$, i.e. its image under the coefficientwise map $\mathbb{Z} \to \mathbb{Z}/p$, is non-zero; and the reductions modulo $p$ of $p_G$ and $p_H$ coincide. Thus the two forms, of weights differing by one, have integral $q$-expansions that are congruent modulo $p$ coefficient by coefficient, the common reduction being non-zero. No sign or size condition is imposed on $k$, and no normalisation of $G$ or $H$ beyond the stated congruence is claimed.
--
--   This is the level-$p$ congruence input expressing, in characteristic zero, the tautological $(p-1)$-st root of the Hasse invariant: a weight-one object with $q$-expansion $1$ modulo $p$, realised here as a pair of forms on $\Gamma_1(p)$ whose weights differ by one and whose integral $q$-expansions agree modulo $p$. It is used in the analysis of the Igusa function field and its Kummer generator, being cited by the results on the Eisenstein ratio and on Gauss reduction in the function field of $X_1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm MatrixGroups

theorem ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ (k : ℤ) (G : ModularForm (Gamma1 p) (k + 1)) (H : ModularForm (Gamma1 p) k)
      (pG pH : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp G pG ∧ ModularCurve.IsIntegralQExp H pH ∧
      pH.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      pG.map (Int.castRingHom (ZMod p)) = pH.map (Int.castRingHom (ZMod p)) := by sorry
