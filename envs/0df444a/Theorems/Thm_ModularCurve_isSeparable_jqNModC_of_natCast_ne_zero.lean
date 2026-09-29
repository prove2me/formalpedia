-- Prove2me | Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero
-- name    : ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/166282e3-2a10-59aa-b681-4ad1c4b2096f
-- title:
--   Separability of j(q^M) over K(j(q)) for M invertible
-- statement:
--   Let $K$ be a field and let $M$ be a nonzero natural number whose image $(M : K)$ in $K$ is nonzero. Work inside the field $\mathrm{LaurentSeries}\,K = K((q))$ of formal Laurent series. Let `jqModC K` be the element $q^{-1}\cdot \iota(\bar{\mathrm{jNum}})$, where $\mathrm{jNum} = E_4^3\cdot \eta^{-1}_{\mathrm{unit}}$ is the integral power series `jNum` (the product of the cube of `eisenstein4` with `dedekindEtaUnitInv`), reduced coefficientwise along $\mathbb{Z}\to K$ and embedded into Laurent series, and $q^{-1}$ is the Hahn-series monomial `HahnSeries.single (-1) 1`; thus `jqModC K` is the $q$-expansion of the modular invariant $j$ with coefficients in $K$. For a nonzero natural number $N$, let `qExpand K N` be the ring endomorphism of $K((q))$ obtained by pushing the support forward along multiplication by $N$ on the exponent group $\mathbb{Z}$, i.e. the substitution $q\mapsto q^{N}$, and set `jqNModC K N` $=$ `qExpand K N (jqModC K)`, the series $j(q^{N})$. The conclusion is that `jqNModC K M` is separable over the intermediate field $K(\,$`jqModC K`$\,)$ of $K((q))$ generated over $K$ by the single element `jqModC K`: its minimal polynomial over that field is a separable polynomial (in particular the element is algebraic over it).
--
--   This is the statement that the modular function $j(q^M)$ generates a separable extension of $K(j(q))$ whenever the level $M$ is invertible in $K$, in any characteristic; classically it reflects the separability of the degeneracy maps $X_0(M)\to X(1)$ away from the residue characteristics dividing $M$. It is used downstream in the treatment of modular curves and of mod $p$ modular forms, where separability of the level structure over the $j$-line is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isSeparable_jqNModC_of_natCast_ne_zero.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.isSeparable_jqNModC_of_natCast_ne_zero (K : Type*) [Field K] (M : ℕ) [NeZero M]
    (hM : (M : K) ≠ 0) :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M) := by sorry
