-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
-- name    : ModularCurve.MultCovering.exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/88f3c41f-adde-51d9-b196-8005c522a8f7
-- title:
--   A simple zero at some supersingular node
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $k = \mathrm{ResidueField}(A)$ has characteristic $p$ (and decidable equality), and let $\Gamma$ be a chart context `ChartCtx p A`: a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-maps in level $1$, a place specialisation over $A$ together with a level-one prolongation pair, a set $S_1$ of places of the level-$p$ function field, the finite set of supersingular places in level $1$ over $k$, and the finiteness of the supersingular $j$-set together with the equality of its cardinality with $m = \mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$, plus a chart supply. Let $f$ be an element of the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $1\cdot p$ (realised inside Laurent series), lying in the valuation subring `integers` of the chart `infChart Γ`, and let $P \in k[X]$ be nonzero with $\deg P + 1 \le m$. Assume the residue of $f$ in $\mathrm{modularFunctionFieldC}\ k\ 1$ equals $\mathrm{ssPolyBar}\,\Gamma \cdot P(\bar\jmath) = \prod_{e : \mathrm{Fin}\,m} (\bar\jmath - \mathrm{ssValue}\,\Gamma\,e) \cdot P(\bar\jmath)$, where $\bar\jmath$ is the $q$-expansion of the $j$-invariant over $k$. Then there exists $e : \mathrm{Fin}\,m$ such that the order of this residue at the place $\mathrm{nodeTgt}\,\Gamma\,e = \mathrm{charLGeomPlaceOfPoint}\,k\,(\mathrm{ssValue}\,\Gamma\,e)$, i.e. minus the logarithm of its adic valuation there, equals $1$.
--
--   This is the assertion that a chart residue of the shape (supersingular polynomial) $\times$ (a nonzero polynomial in $j$ of degree less than the number of supersingular $j$-values) vanishes to order exactly $1$ at at least one supersingular node of the fibre of the $p$-covering: the supersingular factor contributes a simple zero at each node, and $P$ cannot vanish at all $m$ of them. It supplies the node-data input used in the construction of the Hasse member of the good family on the $\bar\infty$-chart, and is cited by [`ModularCurve.MultCovering.FamData.hasseExp_le_one_of_orth`](thm.html#ModularCurve.MultCovering.FamData.hasseExp_le_one_of_orth) and by the comparison results relating orders at nodes on the $\bar 0$- and $\bar\infty$-charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_node_ord_infChart_residue_eq_one_of_eq_ssPolyBar_mul
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    (f : ↥(modularFunctionFieldBar (1 * p))) (hf : f ∈ (infChart Γ).integers)
    (P : Polynomial (IsLocalRing.ResidueField ↥A)) (hP0 : P ≠ 0) (hdeg : P.natDegree + 1 ≤ mAnnuli p)
    (hres : (infChart Γ).residue ⟨f, hf⟩ = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) P) :
    ∃ e : Fin (mAnnuli p), (nodeTgt Γ e).ord ((infChart Γ).residue ⟨f, hf⟩) = 1 := by sorry
