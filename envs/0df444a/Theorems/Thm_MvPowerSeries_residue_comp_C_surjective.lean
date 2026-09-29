-- Prove2me | Theorems.Thm_MvPowerSeries_residue_comp_C_surjective
-- name    : MvPowerSeries.residue_comp_C_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/626e9c89-43fc-5d31-8905-b6407693a3b7
-- title:
--   Residue field of R[[X_σ]] comes from R
-- statement:
--   Let $\sigma$ be any index type and let $R$ be a commutative ring which is local, i.e. carries the `IsLocalRing` structure. Consider the ring $\mathrm{MvPowerSeries}\ \sigma\ R$ of formal power series in the family of variables indexed by $\sigma$ with coefficients in $R$, which is again local, and its residue map $\mathrm{residue}$ onto the quotient by its maximal ideal. The assertion is that the set-theoretic composite of the constant-power-series ring homomorphism $\mathrm{C} : R \to \mathrm{MvPowerSeries}\ \sigma\ R$ with that residue map is a surjective function from $R$ onto the residue field of $\mathrm{MvPowerSeries}\ \sigma\ R$: every class in the residue field of the power series ring is represented by a constant power series. No finiteness hypothesis on $\sigma$ is imposed. The statement is about surjectivity of the composite only; the induced isomorphism between the residue field of $R$ and that of $\mathrm{MvPowerSeries}\ \sigma\ R$ is not formulated.
--
--   This is the standard fact that a power series ring over a local ring has the same residue field as the base, in the form needed to verify residue-field hypotheses for presentations over $\mathcal{O}[[X_1,\dots,X_n]]$. It is used in [`Algebra.PatchingDatum.nonempty_patchingLevel_bot`](thm.html#Algebra.PatchingDatum.nonempty_patchingLevel_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_residue_comp_C_surjective.lean

import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem MvPowerSeries.residue_comp_C_surjective {σ : Type u} {R : Type v} [CommRing R] [IsLocalRing R] : Function.Surjective (⇑(IsLocalRing.residue (MvPowerSeries σ R)) ∘ ⇑(MvPowerSeries.C (σ := σ) (R := R))) := by sorry
