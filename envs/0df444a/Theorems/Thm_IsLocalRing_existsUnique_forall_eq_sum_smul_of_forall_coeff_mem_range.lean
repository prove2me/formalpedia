-- Prove2me | Theorems.Thm_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
-- name    : IsLocalRing.existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/bf244514-cf74-563c-9bef-e6d77ff22c42
-- title:
--   Basis coordinates of a power series with coefficients in ι(V)
-- statement:
--   Let $B$ be a commutative local ring with residue field $k =$ `ResidueField B`, and let $V$ be an abelian group carrying both a $k$-module structure, finite over $k$, and a $B$-module structure, the two being compatible in the sense that $B$ acts on $V$ through $k$ (`IsScalarTower B (ResidueField B) V`). Let $\iota \colon V \to B$ be an injective $B$-linear map, and let $bV$ be a $k$-basis of $V$ indexed by $\mathrm{Fin}\,r$. Let $\tau$ be an index type and let $\Delta \in B[[X_t : t \in \tau]]$ be a multivariate power series each of whose coefficients lies in the image of $\iota$. The conclusion is the conjunction of two assertions. First, there is exactly one family $z = (z_i)_{i < r}$ of power series over $k$ with the property that for every family $zl = (zl_i)_{i<r}$ of power series over $B$ whose coefficientwise reductions satisfy $\mathrm{map}(\mathrm{residue}\,B)(zl_i) = z_i$ for all $i$, one has $\Delta = \sum_{i} \iota(bV_i) \cdot zl_i$ (scalar multiplication of the power series $zl_i$ by the element $\iota(bV_i)$ of $B$). Second, every family $z$ of power series over $k$ does admit such a family of coefficientwise lifts to $B$.
--
--   This is the coefficientwise bookkeeping for a small extension: the ideal $\iota(V) \subseteq B$ is killed by the maximal ideal, so multiplication $\iota(v)\,b$ depends only on the residue of $b$, and a power series with coefficients in $\iota(V)$ has well-defined coordinates over $k$ with respect to a $k$-basis of $V$, any lifts of those coordinates being equally good. It is used in the deformation theory of multivariate formal group laws, in [`MvFormalGroup.Deformation.existsUnique_isShiftBy`](thm.html#MvFormalGroup.Deformation.existsUnique_isShiftBy), [`MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy`](thm.html#MvFormalGroup.Deformation.isIso_of_isShiftBy_of_isShiftBy) and `MvFormalGroup.Deformation.isShiftBy_of_isIso_of_isShiftBy`-type statements, to express the difference of two lifts along a small surjection as $\sum_i \iota(bV_i)\,\tilde z_i$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.existsUnique_forall_eq_sum_smul_of_forall_coeff_mem_range
    {B : Type} [CommRing B] [IsLocalRing B]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    {r : ℕ} (bV : Module.Basis (Fin r) (ResidueField B) V)
    {τ : Type} (Δ : MvPowerSeries τ B) (hΔ : ∀ n, MvPowerSeries.coeff n Δ ∈ LinearMap.range ι) :
    (∃! z : Fin r → MvPowerSeries τ (ResidueField B),
        ∀ zl : Fin r → MvPowerSeries τ B, (∀ i, MvPowerSeries.map (residue B) (zl i) = z i) → Δ = ∑ i, ι (bV i) • zl i) ∧
    (∀ z : Fin r → MvPowerSeries τ (ResidueField B), ∃ zl : Fin r → MvPowerSeries τ B, ∀ i, MvPowerSeries.map (residue B) (zl i) = z i) := by sorry
