-- Prove2me | Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
-- name    : ModularCurve.geomAut_atkinLehner_comp_legs
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/4818530d-6317-5f84-9e01-3a4c062a89af
-- title:
--   Atkin–Lehner automorphism exchanges the two degeneracy legs
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and assumed algebraic over $\mathbb{Q}$, and let $N,\ell$ be nonzero natural numbers. Write $F_M =$ `modularFunctionFieldFull M` for the subfield of $\mathbb{Q}((q))$ (Laurent series over $\mathbb{Q}$) generated over $\mathbb{Q}$ by the series $j(q^{d})$ = `qExpand ℚ d jq` for all nonzero divisors $d$ of $M$, and $L\cdot F_M =$ `laurentBaseChange L F_M` for the subfield of $L((q))$ generated over $L$ by the coefficientwise images of the elements of $F_M$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F_{N\ell}$ satisfying `IsAtkinLehnerAutFull N ℓ`, that is: for every nonzero $d \mid N$ one has $\sigma(j(q^{d})) = j(q^{d\ell})$ and $\sigma(j(q^{d\ell})) = j(q^{d})$. Let `geomAut L F_{N\ell} σ` be the $L$-algebra automorphism of $L\cdot F_{N\ell}$ obtained by transporting $\mathrm{id}_L \otimes \sigma$ through the isomorphism $L \otimes_{\mathbb{Q}} F_{N\ell} \cong L\cdot F_{N\ell}$. Then, with $\bar\alpha =$ `heckeAlphaBar L N ℓ` the inclusion $L\cdot F_N \hookrightarrow L\cdot F_{N\ell}$ and $\bar\beta =$ `heckeBetaBar L N ℓ` the $L$-algebra map $x \mapsto x(q^{\ell})$ given by scaling Hahn-series exponents by $\ell$, the theorem asserts both $\mathrm{geomAut}(\sigma) \circ \bar\alpha = \bar\beta$ and $\mathrm{geomAut}(\sigma) \circ \bar\beta = \bar\alpha$.
--
--   This is the function-field form of the classical fact that the Atkin–Lehner involution $w_\ell$ on $X_0(N\ell)$ interchanges the two degeneracy projections $X_0(N\ell) \rightrightarrows X_0(N)$ whose graph is the Hecke correspondence $T_\ell$. It is the input to the symmetry (transposition) of that correspondence and is used in the analysis of the degeneracy maps on models and their fibres, for instance in identifying the places of the special fibre cut out by cusp charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_geomAut_atkinLehner_comp_legs.lean

import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_GeometricBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.geomAut_atkinLehner_comp_legs (L : Type*) [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ] (σ : modularFunctionFieldFull (N * ℓ) ≃ₐ[ℚ] modularFunctionFieldFull (N * ℓ)) (hσ : IsAtkinLehnerAutFull N ℓ σ) : (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeAlphaBar L N ℓ) = heckeBetaBar L N ℓ ∧ (geomAut L (modularFunctionFieldFull (N * ℓ)) σ).toAlgHom.comp (heckeBetaBar L N ℓ) = heckeAlphaBar L N ℓ := by sorry
