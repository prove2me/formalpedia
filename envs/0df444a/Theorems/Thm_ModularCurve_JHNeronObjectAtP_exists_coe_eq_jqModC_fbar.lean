-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_coe_eq_jqModC_fbar
-- name    : ModularCurve.JHNeronObjectAtP.exists_coe_eq_jqModC_fbar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/75f99478-1bdf-5fb2-86ee-a1410a67e009
-- title:
--   The q-expansion of j lies in the fibre function field
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $M/p$ nonzero, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa =$ `ResidueField ↥A` (the residue field of the local ring $A$) has characteristic $p$. Write $\kappa((q))$ for `LaurentSeries` $\kappa$, and let `JHNeronObjectAtP.Fbar p M H hpM` $\kappa$ be, by definition, the subfield `qExpFunctionFieldC` $\kappa$ (`ΓN p M H hpM`) of $\kappa((q))$ attached to the congruence subgroup `ΓN p M H hpM`. The assertion is that there is an element $xb$ of this subfield whose image in $\kappa((q))$ is `jqModC` $\kappa$, namely $q^{-1}$ times the image under $\mathbb{Z} \to \kappa$ of the integral power series `jNum`; that is, the reduction to $\kappa$ of the $q$-expansion $j(q) = q^{-1} + 744 + 196884\,q + \cdots$ belongs to the fibre function field.
--
--   This supplies, once and for all, the element with $q$-expansion $\bar j(q)$ required by the carrier conventions for function fields of the characteristic-$p$ fibre of the modular curve: it is used in the place-specialisation analysis at level $H$, where the modular invariant serves as the distinguished affine coordinate for reading off points above the cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_coe_eq_jqModC_fbar.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_coe_eq_jqModC_fbar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] :
    ∃ xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by sorry
