-- Prove2me | Theorems.Thm_ModularCurve_kroneckerCentreDichotomy
-- name    : ModularCurve.kroneckerCentreDichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/70e45f8d-8203-5450-979b-85149946269f
-- title:
--   Coupled Kronecker dichotomy at the two degeneracy restrictions
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$, let $\ell$ be a prime and $N$ a nonzero natural number, let $k$ be a field of characteristic $\ell$ and $\mathrm{red} : A \to k$ a ring homomorphism. Assume the pair integrality condition `hKR`: writing $j(q)$ for `jq` and $j(q^{\ell})$ for `jqN ℓ`, and letting `qExpand ℚ N` be the substitution $q \mapsto q^{N}$ on $\mathbb{Q}$-Laurent series, both elements $\ell^{-1}\bigl((j(q^{\ell}) - j(q)^{\ell})\cdot (q\mapsto q^{N})(j(q) - j(q^{\ell})^{\ell})\bigr)$ and $\ell^{-1}\bigl((j(q) - j(q^{\ell})^{\ell})\cdot (q\mapsto q^{N})(j(q^{\ell}) - j(q)^{\ell})\bigr)$ are integral over the subring $\mathbb{Z}[j(q)]$ of $\mathrm{LaurentSeries}\ \mathbb{Q}$. Assume further that the two $\overline{\mathbb{Q}}$-algebra maps `heckeAlphaBar` and `heckeBetaBar` from the base-changed full modular function field of level $N$ to that of level $N\ell$ — the inclusion of levels, and the map induced by $q \mapsto q^{\ell}$ — are integral (`hα`, `hβ`). Let $W$ be a place of the base-changed full modular function field of level $N\ell$, that is, a proper valuation subring containing $\overline{\mathbb{Q}}$ and which is a principal ideal ring, and let $a_j, a_N, b_j, b_N \in A$. The four remaining hypotheses say that at the restriction of $W$ along `heckeAlphaBar` the functions $j(q)$ and $j(q^{N})$ (transported by `coeffEmb`) differ from the images of $a_j$ and $a_N$ by elements of strictly positive `ord`, and likewise that at the restriction of $W$ along `heckeBetaBar` they differ from the images of $b_j$ and $b_N$ by elements of strictly positive `ord`. The conclusion is the dichotomy, coupled across the two coordinates: either $\mathrm{red}\,a_j = (\mathrm{red}\,b_j)^{\ell}$ and $\mathrm{red}\,a_N = (\mathrm{red}\,b_N)^{\ell}$, or $(\mathrm{red}\,a_j)^{\ell} = \mathrm{red}\,b_j$ and $(\mathrm{red}\,a_N)^{\ell} = \mathrm{red}\,b_N$.
--
--   This is the function-field form of Kronecker's congruence $\Phi_{\ell}(X,Y) \equiv (X^{\ell}-Y)(X-Y^{\ell}) \bmod \ell$, read off at a place of the level-$N\ell$ modular function field: the two degeneracy restrictions of the place carry the same pair of $j$-coordinates up to one of the two Frobenius relations, the same alternative for the $j(q)$- and the $j(q^{N})$-coordinate. It is used in the analysis of the geometric fibres of the characteristic-$\ell$ model of the modular curve, namely by [`ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_ne_zero_of_level`](thm.html#ModularCurve.CharPModel.FibreModel.spPlace_d2_of_derivative_evalEval_ne_zero_of_level).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kroneckerCentreDichotomy.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.kroneckerCentreDichotomy
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (hKR : IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jqN ℓ - jq ^ ℓ) * qExpand ℚ N (jq - (jqN ℓ) ^ ℓ)))
      ∧ IsIntegral (Algebra.adjoin ℤ ({jq} : Set (LaurentSeries ℚ)))
        ((ℓ : LaurentSeries ℚ)⁻¹ * ((jq - (jqN ℓ) ^ ℓ) * qExpand ℚ N (jqN ℓ - jq ^ ℓ))))
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (W : Place (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))))
    (aj aN bj bN : A)
    (haj : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aj : AlgebraicClosure ℚ)))
    (haN : 0 < (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (aN : AlgebraicClosure ℚ)))
    (hbj : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full N (jq_mem N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bj : AlgebraicClosure ℚ)))
    (hbN : 0 < (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ).ord
      (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (jqd_mem_full N (dvd_refl N))⟩
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
            (bN : AlgebraicClosure ℚ))) :
    (red aj = red bj ^ ℓ ∧ red aN = red bN ^ ℓ)
      ∨ (red aj ^ ℓ = red bj ∧ red aN ^ ℓ = red bN) := by sorry
