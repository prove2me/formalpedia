-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_FamData_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
-- name    : ModularCurve.MultCovering.FamData.residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c4b7f46a-a02c-58d0-88cb-03d85c28efed
-- title:
--   Regularity off the nodes of the rescaled family on the ̄ 0-chart
-- statement:
--   Fix a prime $p$ (as a `Fact`) and $r \in \mathbb{N}$, and let $D$ be a datum of type `FamData p r`, that is: a family $t_0,\dots,t_{r-1}$ of elements of `modularFunctionFieldBar (1 * p)` together with rational representatives $\mathrm{tRat}_l$ in `modularFunctionFieldFull (1 * p)` such that each $t_l$ is obtained from $\mathrm{tRat}_l$ by the coefficient embedding $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$ on Laurent series. Assume the predicate `IsEmbBasis (1 * p) D.t` for the family, and assume the orthogonality condition at the cusp $0$: for every $c \colon \mathrm{Fin}\,r \to \mathbb{Q}$, all Laurent coefficients of $\sum_i c_i \cdot \mathrm{frickeInvolutionFull}(1 \cdot p)(\mathrm{tRat}_i)$ have non-negative $p$-adic valuation if and only if $-n_i \le v_p(c_i)$ for every $i$, where $n_i =$ `hasseExp D i` is the natural-number truncation of the least $p$-adic valuation attained by the nonzero coefficients of the Laurent expansion of $\mathrm{frickeInvolutionFull}(1 \cdot p)(\mathrm{tRat}_i)$ (and $0$ if no such least value exists). Let further $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, with decidable equality and characteristic $p$ on its residue field, and let $\Gamma$ be a chart context `ChartCtx p A` (a modular polynomial datum satisfying the Kronecker congruence, integrality of the Hecke $\alpha$- and $\beta$-expansions, a place specialisation with a level-one prolongation pair, a set $S_1$ of places, the finset of supersingular places of the special fibre, and the finiteness of the supersingular $j$-set with cardinality $\mathrm{mAnnuli}\,p$, together with the chart supply data). Finally, assume that for every $l$ the rescaled element $\mathrm{goodFamilyZero}\,D\,l = (p^{n_l})^{-1} t_l$ lies in the valuation subring `(zeroChart Γ).integers` of the chart $\mathrm{zeroChart}\,\Gamma$, obtained from $\mathrm{infChart}\,\Gamma$ by pullback along the Fricke involution. The conclusion is that for every index $l$ and every place $v$ of `modularFunctionFieldC (ResidueField A) 1` over the residue field of $A$ which is not one of the finitely many nodes of $\mathrm{zeroChart}\,\Gamma$, the order of the residue of $(p^{n_l})^{-1} t_l$ at $v$ is non-negative.
--
--   On the Deligne–Rapoport model of $X_0(p)$ over a valuation ring above $p$ the special fibre consists of two rational components meeting at the supersingular points, the two components being interchanged by the Fricke involution; the chart $\mathrm{zeroChart}\,\Gamma$ is the component chart at the cusp $0$, realised as the pullback of the chart at $\infty$ along the involution. The assertion is that after the $p$-power rescaling dictated by the $p$-adic content $n_l$ of the $q$-expansion of $w_p t_l$, the reduction of $t_l$ on the zero component has no poles away from the nodes. This is stated in hypothesis form: the orthogonality of the family at the cusp $0$ and the integrality of the rescaled members on the zero chart are assumed rather than proved, and only the order at non-node places is asserted. It is one of the inputs to [`ModularCurve.MultCovering.FamData.t_zeroChart_of_orth`](thm.html#ModularCurve.MultCovering.FamData.t_zeroChart_of_orth), which verifies the zero-chart requirement in the structure `FamCtx`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_FamData_residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

theorem ModularCurve.MultCovering.FamData.residue_goodFamilyZero_ord_nonneg_of_not_mem_nodes (p : ℕ) [Fact p.Prime] {r : ℕ} (D : FamData p r) (hbasis : IsEmbBasis (1 * p) D.t)
    (horthZero : ∀ c : Fin r → ℚ,
      (∀ m : ℤ, 0 ≤ padicValRat p (((∑ i, c i • frickeInvolutionFull (1 * p) (D.tRat i) :
        ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m))
        ↔ ∀ i, -((hasseExp D i : ℕ) : ℤ) ≤ padicValRat p (c i))
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)
    (hint : ∀ l, goodFamilyZero D l ∈ (zeroChart Γ).integers) :
    ∀ (l : Fin r) (v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)),
      v ∉ (zeroChart Γ).nodes → 0 ≤ v.ord ((zeroChart Γ).residue ⟨goodFamilyZero D l, hint l⟩) := by sorry
