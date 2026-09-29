-- Prove2me | Theorems.Thm_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop
-- name    : ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/898cbf01-d4c7-58b7-8d36-40dbe2a2e888
-- title:
--   Exchanging j and j(q^ℓ) preserves the Gauss valuation ring
-- statement:
--   Fix primes $p$ and $\ell$ with $p \ne \ell$, a nonzero natural number $N$ with $p \nmid N$ and $\ell \nmid N$, and a subgroup $H' \le (\mathbb{Z}/N)^{\times}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of `LiesOverPrime`, i.e. the image of $p$ is a nonunit of $A$. Let $F'$ be an intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ equal to `laurentBaseChange` of `xHTopFunctionFieldC ℚ N H' (N * ℓ)`, that is, the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the field $\mathbb{Q}\bigl(\text{intFormRatiosC}\bigr)$ attached to the group $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$, where $\Gamma_{H'}(N)$ is the preimage in $\Gamma_0(N)$ of $H'$ under the diagonal-unit map. Let $j, j_\ell \in F'$ be the elements whose Laurent series are `jqModC`, namely $q^{-1}$ times the power series `jNum` $= E_4^3 \cdot \eta$-unit-inverse over $\overline{\mathbb{Q}}$, and its image under `qExpand` at $\ell$ (multiplication by $\ell$ on exponents, $q \mapsto q^{\ell}$). Let $W_0$ be a valuation subring of $F'$ consisting exactly of those $f$ admitting a Gauss presentation over $A$: power series $x, y$ with coefficients in $A$, the coefficientwise reduction of $y$ to the residue field of $A$ nonzero, and $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$. Let $w$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $F'$ with $w(j) = j_\ell$ and $w(j_\ell) = j$. Then for every $f \in F'$ one has $w(f) \in W_0$ if and only if $f \in W_0$; equivalently $w(W_0) = W_0$.
--
--   This is the good-reduction stability statement for the Gauss point of the modular curve of level $\Gamma_{H'}(N) \cap \Gamma_0(N\ell)$: since the residue characteristic $p$ divides neither $N$ nor $\ell$, the Atkin–Lehner-type involution interchanging $j$ and $j(q^{\ell})$ cannot move the valuation ring cut out by $A$-integral $q$-expansions. It is used in the construction of the reduction in characteristic $p$ of the function field together with its diamond and Hecke operators, where the compatibility of the two degeneracy maps at $\ell$ is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_j_eq_of_liesOverPrime_xHTop
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]
    (hpN : ¬ p ∣ N) (hpℓ : p ≠ ℓ) (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (F' : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hF' : F' = ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.xHTopFunctionFieldC ℚ N H' (N * ℓ)))
    (j jℓ : ↥F') (hj : ((j : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hjℓ : ((jℓ : LaurentSeries (AlgebraicClosure ℚ))) = ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (ModularCurve.jqModC (AlgebraicClosure ℚ)))
    (W₀ : ValuationSubring ↥F')
    (hW₀ : ∀ f : ↥F', f ∈ W₀ ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))))
    (w : ↥F' ≃ₐ[AlgebraicClosure ℚ] ↥F') (hwj : w j = jℓ) (hwjℓ : w jℓ = j) :
    ∀ f : ↥F', w f ∈ W₀ ↔ f ∈ W₀ := by sorry
