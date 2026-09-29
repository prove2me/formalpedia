-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_le_modulusExp
-- name    : ModularCurve.MultCovering.hasseExp_le_modulusExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/24533886-f936-5c86-8ea5-130014339e5a
-- title:
--   Hasse exponents bounded by the modulus exponent 3
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that the image of $p$ lies in the nonunits of $A$, with residue field of characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$: a package consisting of modular polynomial data at $p$, the Kronecker congruence for it, integrality of the two Hecke maps $\bar\alpha$, $\bar\beta$ at level $1$ and prime $p$ over $\overline{\mathbb Q}$, a specialisation $P$ of places of $A$ together with a level-one prolongation pair $R$, a set $S_1$ of places of the base-changed modular function field of level $1\cdot p$, a finite set of places of the level-one modular function field over the residue field of $A$ enumerating the supersingular places, and the finiteness of the supersingular $j$-set with cardinality $\mathrm{mAnnuli}\,p$, plus a chart supply condition for $S_1$. Let $\Delta$ be an annulus context over $\Gamma$: two families $\mathrm{An}_e$, $\mathrm{An}'_e$ of annuli over $A$ in the field $\overline{\mathbb Q}$-modular functions of level $1\cdot p$, indexed by $e<\mathrm{mAnnuli}\,p$, with equal domains and moduli, nonzero modulus, product of parameters equal to the common modulus, domains the places supersingularly centred at the value $\mathrm{ssValue}\,\Gamma\,e$, parameter equal to $\mathrm{tieG}\,p$ away from $j=0,1728$, modulus $p^{\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$, and attachment of $\mathrm{An}_e$, $\mathrm{An}'_e$ to the source and target charts at the corresponding nodes. Finally let $\Phi$ be a family context for $p$ of rank $r$: underlying family data whose functions $t_l$ form an embedding basis (linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of the embedding divisor at level $1\cdot p$), with $t_0=1$, together with the conditions on reductions in the chart at infinity and in the zero chart described by the fields of that structure. Then for every index $l<r$ the Hasse exponent $\mathrm{hasseExp}$ of the underlying family data at $l$, that is the natural-number truncation of the integer $\mathrm{hasseContent}$, is at most $\mathrm{modulusExp}=3$.
--
--   This is the uniform bound on the $p$-adic content exponents of the members of a good family of functions on $X_0(p)$ by the maximal width $3$ of a supersingular node, obtained by traversing the supersingular annuli whose moduli are $p^{\mathrm{jWidth}}$ with $\mathrm{jWidth}\in\{1,2,3\}$. It feeds the comparison results between the chart at infinity and the zero chart, in particular the comparison lemmas for the rescaled family and the bound used in the small-$p$ cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_le_modulusExp.lean

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

theorem ModularCurve.MultCovering.hasseExp_le_modulusExp (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) :
    ∀ l : Fin r, hasseExp Φ.toFamData l ≤ modulusExp := by sorry
