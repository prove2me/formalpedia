-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_nonempty_annCtx
-- name    : ModularCurve.MultCovering.nonempty_annCtx
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/69777f7b-7929-5c84-a358-f1b163b680d7
-- title:
--   Nonemptiness of the annulus context over a chart context
-- statement:
--   Let $p$ be a prime with $5 \le p$ and let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $k =$ `IsLocalRing.ResidueField ↥A` has characteristic $p$ and is algebraically closed, and let $\Gamma$ be a chart context `ChartCtx p A` (modular polynomial data with the Kronecker congruence, integrality of the two Hecke parameters, a place specialisation $P$ over $A$ at level $1$ together with a level-one prolongation pair, a set $S_1$ of places of $\overline{\mathbb Q}$-function field $\overline{F}_{1\cdot p}$ with the chart supply laws, the finite set of supersingular places, and the finiteness of the supersingular $j$-set with cardinality $\mathrm{mAnnuli}\,p$). The assertion is that the type `AnnCtx Γ` is nonempty, i.e. there exist two families $\mathrm{An}_e, \mathrm{An}'_e$ of annuli over $A$ in $\overline{F}_{1\cdot p}$, indexed by $e \in \mathrm{Fin}(\mathrm{mAnnuli}\,p)$ — each an annulus in the sense of the project's `Annulus` structure: a set of rational places, a parameter, and a modulus in the maximal ideal of $A$, subject to the axioms on evaluation of the parameter, the unique-place property for each admissible value, order one for $\mathrm{param} - \mathrm{evalAt}(\mathrm{param})$, and the unit principle — such that for every $e$: $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus; the modulus is nonzero in $\overline{\mathbb Q}$ and equals $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ in $A$, where $\mathrm{jWidth}$ is $3$ at $0$, $2$ at $1728$ and $1$ otherwise; the product of the two parameters is the image of that modulus; the domain of $\mathrm{An}_e$ consists exactly of the places $W$ that are supersingularly centred at $\mathrm{ssValue}\,\Gamma\,e$, that is, for which there are $x, y \in A$ with residues $\mathrm{ssValue}\,\Gamma\,e$ and $(\mathrm{ssValue}\,\Gamma\,e)^p$ such that $W$ has positive order at $j - x$ and at $j_{\mathfrak q} - y$; the parameter of $\mathrm{An}_e$ equals $\mathrm{tieG}\,p = j_{\mathfrak q} - j^{\,p}$ whenever $\mathrm{ssValue}\,\Gamma\,e$ is neither $0$ nor $1728$; and $\mathrm{An}_e$, resp. $\mathrm{An}'_e$, is attached (in the sense of [`AlgebraicCurve.Annulus.IsAttached`](def/AlgebraicCurve_SemistableCharts.html#L115): the node lies in the chart's node set, the parameter is a chart integer whose residue has order $1$ at the node, and the unit comparison holds for chart integers with nonzero residue that are invertible on the annulus) to the chart $\mathrm{chart}\,\Gamma\,(\mathrm{src}\,p\,e)$ at the node $\mathrm{nodeSrc}\,\Gamma\,e$, resp. to $\mathrm{chart}\,\Gamma\,(\mathrm{tgt}\,p\,e)$ at $\mathrm{nodeTgt}\,\Gamma\,e$.
--
--   This is the existence half of the supersingular annuli of the reduction of $X_0(p)$ modulo $p$ — the edges joining the two components of the Deligne–Rapoport model, with local equation $xy = p^{\,\mathrm{jWidth}(a)}$ at a supersingular value $a$ — packaged as an inhabitant of the project's annulus context over a given chart context. It is used by the constructions of family contexts over $X_0(p)$, including [`ModularCurve.MultCovering.exists_famCtx`](thm.html#ModularCurve.MultCovering.exists_famCtx) and the linear-independence statements for residues on the zero chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_nonempty_annCtx.lean

import Definitions.Def_ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.nonempty_annCtx
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (Γ : ChartCtx p A) : Nonempty (AnnCtx Γ) := by sorry
