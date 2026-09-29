-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
-- name    : ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/ace3a2c9-899c-5569-a7ee-474d30bdc46e
-- title:
--   Atkin–Lehner involution swaps degeneracies and width-adjoints Uₛ
-- statement:
--   Fix naturals $M, s, q'$ with $M, s$ nonzero, $q'$ prime, $s$ prime, $q' \ge 5$, $s \neq q'$, and $q' \nmid M$, $s \nmid M$; let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa = \mathrm{ResidueField}(A)$ has characteristic $q'$, and assume the sets $\mathrm{ssPlaces}\,q'\,(Ms)\,\kappa$ and $\mathrm{ssPlaces}\,q'\,M\,\kappa$ of places of the function fields `modularFunctionFieldC` at levels $Ms$ and $M$ satisfying `IsSupersingularPlace` are finite. Let $X$ be an `SSLevelDatum` for $q'$, $\kappa$, $M$, $s$: that is, the $q$-expansions `jqNModC` at levels $M$ and $s$ lie in `modularFunctionFieldC` $\kappa\,(Ms)$, the resulting level maps `levelAlphaC`, `levelBetaC` and all Hecke legs `heckeAlphaC`, `heckeBetaC` are integral, restriction along the two level maps sends supersingular places at level $Ms$ to supersingular places at level $M$ (giving $X.\mathrm{fst}$ and $X.\mathrm{snd}$), together with an Atkin–Lehner $\kappa$-automorphism of `modularFunctionFieldC` $\kappa\,(Ms)$ satisfying `IsAtkinLehnerLevelAut` and stabilising the supersingular places (giving the map $\pi = X.\mathrm{atkinLehnerPerm}$ on them), plus modular polynomial data at $q'$ satisfying the Kronecker congruence. Writing $w\,W = \mathrm{placeWidth}\,(Ms)\,W$ as a positive natural and $U = X.\mathrm{edgeHecke}\,\langle s, hs\rangle$ for the integer matrix indexed by supersingular places at level $Ms$, the conclusion is the conjunction, for all such $W, W'$: $X.\mathrm{fst}(\pi W) = X.\mathrm{snd}\,W$; $X.\mathrm{snd}(\pi W) = X.\mathrm{fst}\,W$; $\pi(\pi W) = W$; $w(\pi W) = w(W)$; and $w(W)\,U(\pi W, \pi W') = w(W')\,U(W', W)$ in $\mathbb{Z}$.
--
--   These are the classical compatibilities of the Atkin–Lehner involution $w_s$ on the supersingular points at the level prime $s$: it exchanges the two degeneracy maps to level $M$, is an involution preserving the widths, and conjugates the Hecke matrix $U_s$ into its adjoint for the width-weighted pairing. They supply the orientation data used by the companion laws for the degeneracy and Hecke matrices and by the rank comparisons for the character lattices of the associated ribbon.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), X.fst (X.atkinLehnerPerm W) = X.snd W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), X.snd (X.atkinLehnerPerm W) = X.fst W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        X.atkinLehnerPerm (X.atkinLehnerPerm W) = W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        X.degeneracyData.w (X.atkinLehnerPerm W) = X.degeneracyData.w W) ∧
    (∀ W W' : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        (X.degeneracyData.w W : ℤ) * X.edgeHecke ⟨s, hs⟩ (X.atkinLehnerPerm W) (X.atkinLehnerPerm W') =
          (X.degeneracyData.w W' : ℤ) * X.edgeHecke ⟨s, hs⟩ W' W) := by sorry
