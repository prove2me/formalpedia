-- Prove2me | Theorems.Thm_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
-- name    : ModularCurve.exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/5f763326-0295-5d34-84e5-5efa67686074
-- title:
--   Descent of the modular equation Φ_ℓ to a q-series subfield
-- statement:
--   Let $\kappa$ be a field, let $\ell$ be a prime, let $\zeta$ be a unit of $\kappa$ whose underlying element is a primitive $\ell$-th root of unity, and let $e$ be a nonzero natural number not divisible by $\ell$. Write $\bar\jmath =$ `jqModC κ` for the Laurent series $q^{-1}\cdot(\text{image in }\kappa\text{ of }E_4^3\cdot\eta\text{-unit inverse})$, i.e. the $q$-expansion of the modular invariant with coefficients read in $\kappa$; write `qExpand κ N` for the ring endomorphism of $\kappa((q))$ substituting $q \mapsto q^N$ (multiplication by $N$ on exponents) and `qTwist u` for the ring endomorphism multiplying the coefficient of $q^k$ by $u^k$, i.e. $q\mapsto uq$. Let $F$ be an intermediate field of $\kappa \subseteq \mathrm{LaurentSeries}\,\kappa$ containing `qExpand κ (ℓ * e) (jqModC κ)`, that is $\bar\jmath(q^{\ell e})$. Then there is a monic polynomial $P \in F[X]$ with $\deg P = \ell + 1$ whose image under the coefficientwise inclusion $F \hookrightarrow \kappa((q))$ equals $$\Bigl(\prod_{k=0}^{\ell-1}\bigl(X - \mathrm{qTwist}(\zeta^k)\,\bar\jmath(q^{e})\bigr)\Bigr)\cdot\bigl(X - \bar\jmath(q^{\ell\cdot\ell e})\bigr),$$ the twisted factors being $X$ minus the constants $\bar\jmath(\zeta^k q^e)$.
--
--   This is the statement that the classical modular equation of prime level $\ell$, evaluated at $\bar\jmath(q^{\ell e})$, has coefficients in any subfield $F$ of $\kappa((q))$ containing that series, while over $\kappa((q))$ it splits with the expected $\ell+1$ roots $\bar\jmath(\zeta^k q^e)$ and $\bar\jmath(q^{\ell^2 e})$. It is used to bound the degree of $\bar\jmath(q^{e})$ over the Igusa function field of $X_1$-type level structure and to deduce non-membership of $\bar\jmath(q^{e})$ in it when $\ell \nmid e$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C.lean

import Mathlib
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial
open ModularCurve

universe u

theorem ModularCurve.exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
    (κ : Type u) [Field κ] (ℓ : ℕ) [Fact ℓ.Prime] (ζ : κˣ) (hζ : IsPrimitiveRoot (ζ : κ) ℓ)
    (e : ℕ) [NeZero e] (heℓ : ¬ ℓ ∣ e)
    (F : IntermediateField κ (LaurentSeries κ))
    (hmem : ModularCurve.qExpand κ (ℓ * e) (ModularCurve.jqModC κ) ∈ F) :
    ∃ P : Polynomial ↥F, P.Monic ∧ P.natDegree = ℓ + 1 ∧
      P.map (algebraMap ↥F (LaurentSeries κ)) =
        (∏ k ∈ Finset.range ℓ,
            (Polynomial.X - Polynomial.C (ModularCurve.qTwist (ζ ^ k) (ModularCurve.qExpand κ e (ModularCurve.jqModC κ))))) *
          (Polynomial.X - Polynomial.C (ModularCurve.qExpand κ (ℓ * (ℓ * e)) (ModularCurve.jqModC κ))) := by sorry
