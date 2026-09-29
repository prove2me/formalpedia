-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero
-- name    : ModularCurve.MultCovering.hasseExp_eq_jWidth_of_genus_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/a8de6667-54c4-585d-9d54-f8e99360dadf
-- title:
--   Hasse exponent equals supersingular node width, genus zero
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that the image of $p$ lies in the nonunits of $A$, with residue field $k = \mathrm{ResidueField}\,A$ of characteristic $p$. Let $\Gamma$ be a chart context for $p$ and $A$ (modular polynomial data satisfying the Kronecker congruence, integrality of the Hecke $\bar\alpha,\bar\beta$ at level $1$, a place specialisation with a level-one prolongation pair, the finite set $\mathrm{ssJSet}$ of supersingular $j$-values in $k$ enumerated by $\mathrm{Fin}(\mathrm{mAnnuli}\,p)$ with $\mathrm{mAnnuli}\,p = \lfloor p/12\rfloor + [p\equiv 2 \bmod 3] + [p\equiv 3 \bmod 4]$, and a chart supply), and let $\Delta$ be an annulus context over $\Gamma$: for each index $e$ a pair of annuli with common domain the places supersingularly centred at $\mathrm{ssValue}\,\Gamma\,e$, with common modulus $p^{\,\mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)}$ in $A$, parameters multiplying to that modulus, and attached to the source and target charts at the two nodes. Let $\Phi$ be a family context with two members, i.e. functions $t_0,t_1$ in $\overline{\mathbb Q}$-rational modular functions of level $1\cdot p$ forming an embedding basis with $t_0 = 1$, together with the $\infty$-chart and $\bar 0$-chart integrality, reduction, linear independence and spanning conditions of `FamCtx`. Assume each rescaled member $\mathrm{goodFamilyZero}\,\Phi\,l = p^{-\mathrm{hasseExp}\,\Phi\,l}\,t_l$ lies in the integers of the zero chart $\mathrm{zeroChart}\,\Gamma$ (the $\infty$-chart pulled back along the Fricke involution), and that the two residues of these elements are linearly independent over $k$. Let $\mu$ be an absolute value on $\overline{\mathbb Q}$ with $a \in A \iff \mu(a)\le 1$. Then for every index $e$ one has $\mathrm{hasseExp}\,\Phi\,1 = \mathrm{jWidth}(\mathrm{ssValue}\,\Gamma\,e)$, where $\mathrm{hasseExp}$ is the truncation to $\mathbb N$ of $\mathrm{hasseContent}$ and $\mathrm{jWidth}(j)$ equals $3$, $2$ or $1$ according as $j = 0$, $j = 1728$ or neither.
--
--   This identifies the $p$-power scaling exponent of the non-constant member of a two-element good family with the width of the supersingular node, i.e. the exponent $e$ in the local equation $xy = p^{e}$ at a supersingular point of the prime-level covering, so that $\mathrm{jWidth}$ records the order of the automorphism group at $j = 0$ and $j = 1728$. It is used in [`ModularCurve.MultCovering.crossComparison_annIn_zeroChart`](thm.html#ModularCurve.MultCovering.crossComparison_annIn_zeroChart) and in the construction of uniform multicoverings with a certified family for primes at least $5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_hasseExp_eq_jWidth_of_genus_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.hasseExp_eq_jWidth_of_genus_zero (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (Φ : FamCtx p 2)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin 2 => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∀ e : Fin (mAnnuli p), hasseExp Φ.toFamData 1 = jWidth (ssValue Γ e) := by sorry
