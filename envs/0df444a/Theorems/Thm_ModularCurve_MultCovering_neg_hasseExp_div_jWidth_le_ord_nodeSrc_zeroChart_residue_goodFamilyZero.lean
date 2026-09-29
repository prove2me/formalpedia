-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
-- name    : ModularCurve.MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/9233f380-fefd-5de6-b1d4-1d931a1ed9c0
-- title:
--   Pole bound at tube nodes for the rescaled good family
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that $p$ is a nonunit of $A$ (the content of `A.LiesOverPrime p`), with residue field $k =$ `ResidueField A` of characteristic $p$; let $\Gamma$ be a chart context `ChartCtx p A` for level $1\cdot p$ and $\Delta$ an annulus context `AnnCtx Γ` over it, so that for each index $e$ among the $m =$ `mAnnuli p` $= \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ annuli the two attached annuli $\mathrm{An}\,e$, $\mathrm{An}'\,e$ have common domain, equal moduli $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ (where $\mathrm{jWidth}(j)$ is $3$, $2$ or $1$ according as $j = 0$, $j = 1728$ or neither), product of parameters equal to the modulus, and are attached to the charts at the nodes $\mathrm{nodeSrc}\,\Gamma\,e$, $\mathrm{nodeTgt}\,\Gamma\,e$. Let $r$ be a natural number and $\Phi$ a family context `FamCtx p r`, with underlying data $\Phi.\mathrm{toFamData}$ giving functions $t_l \in \overline{\mathbb{Q}}(X_0(p))$ and exponents $n_l = \mathrm{hasseExp}\,\Phi\,l \in \mathbb{N}$. The assertion is that the rescaled elements $\mathrm{goodFamilyZero}\,\Phi\,l = p^{-n_l} t_l$ all lie in the valuation subring $(\mathrm{zeroChart}\,\Gamma).\mathrm{integers}$ — where $\mathrm{zeroChart}\,\Gamma$ is the pullback of $\mathrm{infChart}\,\Gamma$ along the Fricke involution in level $1\cdot p$ — and that, for the resulting reductions, for every annulus index $e$ and every $l$,
--   $$-\big\lfloor n_l / \mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)\big\rfloor \le \operatorname{ord}_{\mathrm{nodeSrc}\,\Gamma\,e}\!\big((\mathrm{zeroChart}\,\Gamma).\mathrm{residue}(p^{-n_l} t_l)\big),$$
--   the division being truncated division of natural numbers and $\operatorname{ord}$ the integer order at the place $\mathrm{nodeSrc}\,\Gamma\,e$, which is the place of the level-one function field over $k$ attached to the point $j = (\mathrm{ssValue}\,\Gamma\,e)^p$.
--
--   This is the pole bound, at the node lying on the source side of the $e$-th supersingular tube, for the reductions on the $\bar 0$-chart of the family rescaled by the $p$-adic content of its $q$-expansion at the $0$-cusp: the order of vanishing drops by at most $\lfloor n_l / w_e \rfloor$, where $w_e \in \{1,2,3\}$ is the width of the tube. It is used in the construction of family data with prescribed Hasse exponents and separation properties, in particular in the analysis of wide nodes ($w_e \ne 1$) and in the explicit case $p = 11$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero.lean

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

theorem ModularCurve.MultCovering.neg_hasseExp_div_jWidth_le_ord_nodeSrc_zeroChart_residue_goodFamilyZero (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers,
      ∀ (e : Fin (mAnnuli p)) (l : Fin r),
        -((hasseExp Φ.toFamData l / jWidth (ssValue Γ e) : ℕ) : ℤ)
          ≤ (nodeSrc Γ e).ord ((zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩) := by sorry
