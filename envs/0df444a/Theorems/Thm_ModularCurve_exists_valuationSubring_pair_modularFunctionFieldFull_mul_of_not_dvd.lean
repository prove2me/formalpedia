-- Prove2me | Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
-- name    : ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/b0c470cf-7271-5121-a481-91e8dd6b9252
-- title:
--   Two valuation rings of ℚ(X₀(Np)) lying over p
-- statement:
--   Let $N \ge 1$ and let $p$ be a prime with $p \nmid N$, and write $F = \mathbb{Q}(\mathfrak q^d\text{-expansions})$ for `modularFunctionFieldFull (N * p)`, the subfield of $\mathbb{Q}((\mathfrak q))$ generated over $\mathbb{Q}$ by the series $j(\mathfrak q^d)$ for the nonzero divisors $d$ of $Np$. The assertion is that there are two valuation subrings $W_0, W_1$ of $F$ such that: (i) $f \in W_0$ exactly when $f \cdot y = x$ in $\mathbb{Q}((\mathfrak q))$ for some $x, y \in \mathbb{Z}((\mathfrak q))$ with the coefficientwise reduction of $y$ modulo $p$ nonzero; (ii) $f \in W_1$ exactly when $\sigma(f) \in W_0$, where $\sigma$ is `atkinLehnerInvolutionFull N p`, namely a chosen $\mathbb{Q}$-algebra automorphism of $F$ interchanging $j(\mathfrak q^{d})$ and $j(\mathfrak q^{dp})$ for every nonzero $d \mid N$ if one exists and the identity otherwise (such an automorphism does exist here, by [`ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd`](thm.html#ModularCurve.exists_isAtkinLehnerAutFull_of_prime_of_not_dvd)); (iii) $W_0 \ne W_1$; (iv) for each $i$, the image of $p$ is a nonunit of $W_i$, for every $P \in \mathbb{Z}[X]$ with nonzero reduction modulo $p$ both $P(j)$ and $P(j)^{-1}$ lie in $W_i$ (with $j =$ `jq` viewed in $F$), and every nonunit $f$ of $W_i$ satisfies $f p^{-1} \in W_i$; and (v) every valuation subring $V$ of $F$ in which $p$ is a nonunit and in which $P(j)$ and $P(j)^{-1}$ lie for all such $P$ equals $W_0$ or $W_1$.
--
--   This is the codimension-one part of the Deligne–Rapoport/Katz–Mazur description of $X_0(Np)$ modulo $p$ for $p \nmid N$ — two components, exchanged by the partial Atkin–Lehner involution, with $p$ a uniformiser on each — rendered purely in terms of valuation rings of the function field presented by $\mathfrak q$-expansions at the cusp $\infty$. It feeds the construction of the integral model package at level $Np$, where the two valuation rings give the two charts used in the Ribet-style level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_AtkinLehnerPartial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
    (N p : ℕ) [NeZero N] [Fact p.Prime] (hpN : ¬ p ∣ N) :
    ∃ W : Fin 2 → ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)),

      (∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W 0 ↔
        ∃ x y : LaurentSeries ℤ, ModularCurve.coeffMap (Int.castRingHom (ZMod p)) y ≠ 0 ∧
          (f : LaurentSeries ℚ) * ModularCurve.coeffMap (Int.castRingHom ℚ) y
            = ModularCurve.coeffMap (Int.castRingHom ℚ) x) ∧

      (∀ f : ↥(ModularCurve.modularFunctionFieldFull (N * p)), f ∈ W 1 ↔
        ModularCurve.atkinLehnerInvolutionFull N p f ∈ W 0) ∧

      W 0 ≠ W 1 ∧

      (∀ i, ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ (W i).nonunits ∧
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P ∈ W i ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P)⁻¹ ∈ W i) ∧
        (∀ f ∈ (W i).nonunits,
          f * ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p)))⁻¹ ∈ W i)) ∧

      ∀ V : ValuationSubring ↥(ModularCurve.modularFunctionFieldFull (N * p)),
        ((p : ℕ) : ↥(ModularCurve.modularFunctionFieldFull (N * p))) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P ∈ V ∧
            (Polynomial.eval₂ (algebraMap ℤ ↥(ModularCurve.modularFunctionFieldFull (N * p)))
              ⟨ModularCurve.jq, ModularCurve.modularFunctionField_le_full (N * p)
                (ModularCurve.jq_mem (N * p))⟩ P)⁻¹ ∈ V) →
        V = W 0 ∨ V = W 1 := by sorry
