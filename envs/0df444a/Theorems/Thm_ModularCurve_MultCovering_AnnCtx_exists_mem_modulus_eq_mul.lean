-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_modulus_eq_mul
-- name    : ModularCurve.MultCovering.AnnCtx.exists_mem_modulus_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/9dc6e975-9ad8-5ea4-806d-844ebfdfd371
-- title:
--   Divisibility of annulus moduli by p
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose residue field has characteristic $p$. Let $\Gamma$ be a chart context `ChartCtx p A`, i.e. a package consisting of modular polynomial data for $p$ satisfying the Kronecker congruence, integrality of the Hecke $\bar\alpha$- and $\bar\beta$-maps at level $1$, a place specialisation $P$ over $A$ together with a level-one prolongation pair $R$, a set $S_1$ of places of the base-changed modular function field of level $1\cdot p$, a finite set $W_n$ enumerating the supersingular places at level $1$ over the residue field of $A$, the finiteness of the supersingular $j$-set together with the statement that it has exactly `mAnnuli p` elements, and the chart supply laws for $R$ and $S_1$. Let $\Delta$ be an annulus context `AnnCtx Γ`: for each index $e$ among the `mAnnuli p` annuli it provides two annuli $\mathrm{An}\,e$, $\mathrm{An}'\,e$ in the function field $\overline{\mathbb{Q}}$-algebra `modularFunctionFieldBar (1 * p)` with equal domains and equal moduli, nonzero modulus, product of the two parameters equal to the modulus, the domain of $\mathrm{An}\,e$ consisting exactly of the places that are supersingularly centred at the value `ssValue Γ e` (both $j$ and $j_q$ reducing to that value, resp. its $p$-th power), parameter equal to `tieG p` whenever `ssValue Γ e` is neither $0$ nor $1728$, modulus equal to $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ in $A$, and attachment of $\mathrm{An}\,e$, $\mathrm{An}'\,e$ to the source and target component charts at the corresponding nodes. The conclusion: for every index $e$ there exists $a \in \overline{\mathbb{Q}}$ with $a \in A$ such that the modulus of $\Delta.\mathrm{annIn}\,e = \mathrm{An}\,e$, viewed in $\overline{\mathbb{Q}}$, equals $p \cdot a$.
--
--   This records the clause of the semistable covering data saying that $p$ divides the modulus of every supersingular annulus, so that all these annuli are genuinely thick. It is used in the construction of a uniform multiplicative covering with certified family for primes $p \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_modulus_eq_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_JWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.AnnCtx.exists_mem_modulus_eq_mul (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) : ∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a := by sorry
