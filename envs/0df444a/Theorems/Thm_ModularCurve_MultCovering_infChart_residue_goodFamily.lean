-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_infChart_residue_goodFamily
-- name    : ModularCurve.MultCovering.infChart_residue_goodFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/022237a9-2fb5-54b6-b37c-31d8aa50a98b
-- title:
--   Reduction of the good family on the ∞̄-chart
-- statement:
--   Let $p$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q}$ satisfying `LiesOverPrime p`, i.e. $p$ is a non-unit of $A$, whose residue field $k =$ `ResidueField A` has characteristic $p$; let $\Gamma$ be a chart context `ChartCtx p A` for $p$ and $A$, let $r$ be a natural number and let $\Phi$ be a family context `FamCtx p r`, with associated family `goodFamily Φ` $= \Phi.t : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar (1 * p)`. The assertion is that every member $\Phi.t_l$ lies in the valuation subring `(infChart Γ).integers` of the $\bar\infty$-component chart attached to $\Gamma$, and that, with respect to the residue homomorphism of that chart into `modularFunctionFieldC k 1`: (i) for each $l$ with $l = 0$ the residue of $\Phi.t_l$ is $1$; and (ii) there is a family of polynomials $P_l \in k[X]$, indexed by $l \in \mathrm{Fin}\,r$, such that for every $l \ge 1$ one has $\deg P_l + 1 \le$ `mAnnuli p` $= \lfloor p/12\rfloor + [p \equiv 2 \bmod 3] + [p \equiv 3 \bmod 4]$ and the residue of $\Phi.t_l$ equals `ssPolyBar Γ` $\cdot\, P_l(\bar\jmath)$, where `ssPolyBar Γ` $= \prod_{e : \mathrm{Fin}(\mathrm{mAnnuli}\,p)} (\bar\jmath - \mathrm{ssValue}\,\Gamma\,e)$ and $\bar\jmath$ is the $q$-expansion class `jBar k`; and the subfamily $(P_l)_{l \ge 1}$ is linearly independent over $k$ and spans exactly the space `Polynomial.degreeLT k (mAnnuli p)` of polynomials of degree less than `mAnnuli p`.
--
--   This records, for a fixed chart context, the behaviour of the chosen family of functions on the $\bar\infty$-component of the reduction of the modular curve of level $p$: the member indexed by $0$ reduces to the constant $1$, while the remaining members reduce to the supersingular polynomial times a $k$-basis of the polynomials of degree $<$ `mAnnuli p` in $\bar\jmath$. It is used in the comparison of annular contributions across the two components and in showing that the reductions of the family on the $\bar\infty$-chart are non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_infChart_residue_goodFamily.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.infChart_residue_goodFamily (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)
    {r : ℕ} (Φ : FamCtx p r) :
    ∃ hint : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers,
      (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩ = 1) ∧
      ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
        (∀ l : Fin r, 1 ≤ (l : ℕ) →
          (P l).natDegree + 1 ≤ mAnnuli p ∧
          (infChart Γ).residue ⟨goodFamily Φ l, hint l⟩
            = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
        Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
          = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p) := by sorry
