-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom
-- name    : ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/e778138d-81b6-54d4-afbc-fadabbca3e6e
-- title:
--   Inf- and zero-charts partition the non-supersingular places
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k =$ `ResidueField A` has characteristic $p$, and let $\Gamma$ be a chart context `ChartCtx p A`: that is, modular polynomial data for $p$ together with a Kronecker congruence, integrality of the Hecke $\alpha$- and $\beta$-data at level $1$ and $p$, a place specialisation $\Gamma.P$ from places of the geometric modular function field $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1}$ to places of `modularFunctionFieldC k 1`, a level-one prolongation pair $\Gamma.R$, a set $\Gamma.S_1$ of places of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot p}$, a finset $\Gamma.Wn$ enumerating exactly the places in `ssPlaces p 1 k`, finiteness of `ssJSet p k` with cardinality `mAnnuli p`, and a `ChartFstSupply` for $\Gamma.S_1$. Assume (separation) that no $W\in\Gamma.S_1$ has its Fricke translate $\overline{w_p}\cdot W$ again in $\Gamma.S_1$, and (covering) that whenever the first reduction $\Gamma.P.\mathrm{redFst}\,W$ is fixed by the square of the geometric-level Frobenius `frobOnPlacesGeomLevel`, is an affine geometric place (both `jGeomGen` and `jNGeomGen` lie in its valuation subring) and does not belong to `ssPlaces p 1 k`, then $W\in\Gamma.S_1$ or $\overline{w_p}\cdot W\in\Gamma.S_1$. Let $W$ be a place of $\overline{\mathbb Q}\cdot F^{\mathrm{full}}_{1\cdot p}$ over $\overline{\mathbb Q}$ which, for every $a$ in `ssJSet p k` (the set of $j\in k$ such that every elliptic curve over $k$ with invariant $j$ has no nonzero $p$-torsion point), is not SS-centred at $a$: there is no $x\in A$ with residue $a$ and $W.\mathrm{ord}(\mathrm{jFun}-x)>0$ together with some $y\in A$ with residue $a^p$ and $W.\mathrm{ord}(\mathrm{jqFun}-y)>0$. Then exactly one of $W\in(\mathrm{infChart}\,\Gamma).\mathrm{dom}$ and $W\in(\mathrm{zeroChart}\,\Gamma).\mathrm{dom}$ holds, where `zeroChart` is the pullback of `infChart` along the Fricke involution $\overline{w_p}$.
--
--   This is the chart half of the partition property of a uniform multiplicative covering of $X_0(p)$ at $p$: away from places centred at a supersingular crossing of the two components of the special fibre, the $\infty$-chart and the $0$-chart cover each place exactly once, the Fricke involution exchanging the strict types and the two cusp sides. It is used in the construction of such a covering, [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_mem_infChart_dom_xor_mem_zeroChart_dom.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem ModularCurve.MultCovering.mem_infChart_dom_xor_mem_zeroChart_dom
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hsep : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      W ∈ Γ.S₁ → frickeInvolutionBar (1 * p) • W ∉ Γ.S₁)
    (hcov : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)),
      frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr
          (frobOnPlacesGeomLevel (ResidueField ↥A) 1 Γ.data Γ.hKr (Γ.P.redFst W)) = Γ.P.redFst W →
      IsAffineGeomPlace (ResidueField ↥A) 1 (Γ.P.redFst W) → Γ.P.redFst W ∉ ssPlaces p 1 (ResidueField ↥A) →
      W ∈ Γ.S₁ ∨ frickeInvolutionBar (1 * p) • W ∈ Γ.S₁)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (hW : ∀ a ∈ ssJSet p (ResidueField ↥A), ¬ IsSSCentred p A W a) :
    Xor (W ∈ (infChart Γ).dom) (W ∈ (zeroChart Γ).dom) := by sorry
