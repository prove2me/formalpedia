-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
-- name    : ModularCurve.MultCovering.neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/6ff9d7b0-8adc-532a-93ad-bb17da81f269
-- title:
--   At most simple poles of the rescaled family on the zero chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, i.e. with $p$ a non-unit of $A$, whose residue field has characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$ (modular polynomial data together with the Kronecker congruence, integrality of the Hecke data $\bar\alpha,\bar\beta$, a place specialisation with a level-one prolongation pair, a set $S_1$ of places of the level-$1\cdot p$ modular function field over $\overline{\mathbb{Q}}$, the finset of supersingular places at level one over the residue field, and the hypothesis that the supersingular $j$-set is finite of cardinality $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p\equiv 3\bmod 4]$, plus the chart supply condition), and let $\Delta$ be an annulus context over $\Gamma$: two families of annuli $An_e, An'_e$ indexed by $e \in \mathrm{Fin}(\mathrm{mAnnuli}\,p)$ with the same domain and modulus, modulus nonzero and equal to $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$, product of parameters the modulus, domains characterised by supersingular centring at $\mathrm{ssValue}\,\Gamma\,e$, parameter $\mathrm{tieG}\,p$ at values away from $0$ and $1728$, and $An_e$, $An'_e$ attached to the charts at the source and target nodes $\mathrm{nodeSrc}\,\Gamma\,e$, $\mathrm{nodeTgt}\,\Gamma\,e$. Let $r \in \mathbb{N}$ and let $\Phi$ be a family context of rank $r$ (family data $t : \mathrm{Fin}\,r \to$ the level-$1\cdot p$ modular function field forming an embedding basis, with $t_0 = 1$ and the prescribed reduction behaviour on the $\infty$- and $0$-charts). Assume all widths are one, in the sense that $\mathrm{ssValue}\,\Gamma\,e \neq 0$ and $\neq 1728$ for every $e$. Then there is a witness that each rescaled element $\mathrm{goodFamilyZero}\,\Phi\,l = p^{-\mathrm{hasseExp}\,\Phi\,l}\, t_l$ lies in the valuation subring $(\mathrm{zeroChart}\,\Gamma).\mathrm{integers}$, where $\mathrm{zeroChart}\,\Gamma$ is the pullback of the $\infty$-chart along the Fricke involution, such that for all $e$ and all $l$ the order of the residue of that element, computed at the place $\mathrm{nodeSrc}\,\Gamma\,e$ (the geometric place at the point $(\mathrm{ssValue}\,\Gamma\,e)^p$) is at least $-1$.
--
--   This is the pole bound on the $\bar 0$-chart for the $p$-rescaled good family on the Deligne–Rapoport model of $X_0(p)$: at each supersingular node the reduction of $p^{-n_l}t_l$ has at worst a simple pole, when all node widths equal one. It feeds the description of the $\bar 0$-chart reductions as polynomials of bounded degree, and is used in the construction of a uniform multiplicative covering with a certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.neg_one_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hw : ∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -1 ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
