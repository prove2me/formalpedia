-- Prove2me | Theorems.Thm_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
-- name    : ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/b8a3332d-c00b-5184-b19f-7f27ba3369a1
-- title:
--   Level-one forms are isobaric in E₄,E₆ mod ℓ≥ 5
-- statement:
--   Let $\ell$ be a prime with $\ell \ge 5$, let $k \in \mathbb{Z}$, and let $f$ be a modular form of weight $k$ for the full modular group $\mathrm{SL}_2(\mathbb{Z})$ (denoted $\mathcal{SL}$). Suppose $T \in \mathbb{Z}[\![q]\!]$ is a power series with integer coefficients whose image under the coefficientwise map $\mathbb{Z} \to \mathbb{C}$ equals the $q$-expansion of $f$ of width $1$. Then there exists a polynomial $\Phi \in \mathbb{F}_\ell[X_0, X_1]$ ($\mathbb{F}_\ell = \mathbb{Z}/\ell$) which is weighted homogeneous of degree $k^{+} = \max(k,0)$ for the weights $\mathrm{wt}(X_0) = 4$, $\mathrm{wt}(X_1) = 6$, such that evaluating $\Phi$ at the pair of power series over $\mathbb{F}_\ell$ obtained by reducing $$Q = 1 + 240\sum_{n \ge 1}\Big(\sum_{d \mid n} d^{3}\Big)q^{n}, \qquad R = 1 - 504\sum_{n \ge 1}\Big(\sum_{d \mid n} d^{5}\Big)q^{n}$$ coefficientwise modulo $\ell$ yields the reduction of $T$ modulo $\ell$.
--
--   This is the mod $\ell$ form of the classical structure theorem that a level-one modular form of weight $k$ is an isobaric polynomial in the Eisenstein series $E_4 = Q$ and $E_6 = R$, together with the $\ell$-integrality of the coefficients of that polynomial for $\ell > 3$. It is cited by [`ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne`](thm.html#ModularForm.sub_one_dvd_weight_of_qExpansion_congr_const_levelOne), the statement that $\ell - 1$ divides the weight of a level-one form whose $q$-expansion is congruent to a constant modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ModularForm.exists_isWeightedHomogeneous_aeval_eq_map_qExpansion_levelOne {ℓ : ℕ}
    (hℓ : ℓ.Prime) (h5 : 5 ≤ ℓ) {k : ℤ} (f : ModularForm 𝒮ℒ k) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑f) :
    ∃ Φ : MvPolynomial (Fin 2) (ZMod ℓ),
      Φ.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) k.toNat ∧
        MvPolynomial.aeval
            (![(PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3).map
                (Int.castRingHom (ZMod ℓ)),
              (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5).map
                (Int.castRingHom (ZMod ℓ))] : Fin 2 → PowerSeries (ZMod ℓ)) Φ =
          T.map (Int.castRingHom (ZMod ℓ)) := by sorry
