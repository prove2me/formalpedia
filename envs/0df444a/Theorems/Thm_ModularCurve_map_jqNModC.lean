-- Prove2me | Theorems.Thm_ModularCurve_map_jqNModC
-- name    : ModularCurve.map_jqNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/fe3a7033-4784-5885-bdf7-455b67a8b3a4
-- title:
--   Coefficientwise maps commute with the q-expansion of j(q^N)
-- statement:
--   Let $R$ and $S$ be commutative rings, let $\varphi : R \to S$ be a ring homomorphism, and let $N$ be a natural number with $N \neq 0$. Here `coeffMap` $\varphi$ denotes the ring homomorphism from formal Laurent series (Hahn series over $\mathbb{Z}$) with coefficients in $R$ to those with coefficients in $S$ obtained by applying $\varphi$ to each coefficient; `jqModC` $R$ denotes the Laurent series $q^{-1}$ times the image in $R[[q]]$, under the coefficientwise integer cast, of the integral power series `jNum`; and `qExpand` $R$ $N$ denotes the ring endomorphism of Laurent series over $R$ that relocates the coefficient at exponent $k$ to exponent $Nk$, i.e. the substitution $q \mapsto q^{N}$, realised as the Hahn-series homomorphism induced by multiplication by $N$ on the exponent group (injective and order preserving since $N > 0$). Writing `jqNModC` $R$ $N$ for `qExpand` $R$ $N$ applied to `jqModC` $R$, the assertion is that `coeffMap` $\varphi$ sends `jqNModC` $R$ $N$ to `jqNModC` $S$ $N$.
--
--   This is the naturality in the coefficient ring of the $q$-expansion of $j(q^{N})$: its coefficients are integers, so they are transported by any ring homomorphism. It is used in the statements about base change of the Laurent-series function fields attached to $X_0(N)$ and $X_1(N)$ and in the computation of the degree over the Hecke subfield.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_jqNModC.lean

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.map_jqNModC {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap φ (jqNModC R N) = jqNModC S N := by sorry
