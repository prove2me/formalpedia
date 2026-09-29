-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope
-- name    : ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_telescope
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/caeb0b95-e68d-57b6-9904-e3e7a0eb5f53
-- title:
--   Transport of semistable model to the Fin-indexed telescope
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number, $A$ a valuation subring of $\overline{\mathbb{Q}}$, and $W$ a finite set of places of the field $\mathrm{modularFunctionFieldC}\,(\mathrm{ResidueField}\,A)\,M'$ over the residue field of $A$. Let $\mathcal{C}$ be a semistable covering `SemistableCovering q M' A W`, whose ambient field is $\mathrm{fieldBar}\,q\,M'$, the function field over $\overline{\mathbb{Q}}$ of the modular curve $X_H$ of level $q^2M'$ with $H$ the kernel of the reduction $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$. Assume given a `SemistableModel` $M$ over $A$ for this field with respect to the sum-indexed data of $\mathcal{C}$: vertices indexed by $\mathbb{P}^1(\mathbb{Z}/q)\sqcup W$ with residue fields $\mathcal{C}.\mathrm{sumFbar}$ and charts $\mathcal{C}.\mathrm{sumChart}$, edges indexed by $\mathbb{P}^1(\mathbb{Z}/q)\times W$ with annuli $(\ell,s)\mapsto\mathcal{C}.\mathrm{An}\,\ell\,s$, source and target the vertices $\mathrm{inl}\,\ell$ and $\mathrm{inr}\,s$, and end places given by $\mathcal{C}.\mathrm{sumNode}$ at those vertices; that is, an integral scheme $M.X$, proper, flat and locally of finite presentation over $\mathrm{Spec}\,A$, with an identification of the field with its function field compatible with $A$, together with the points classifying places, component generic points, smooth chart points and nodes. Assume also given a descent datum $D$ for $M$, i.e. a presentation of $M.X$ as a base change of a model over a noetherian Henselian local subring of $A$. Then there exist a `SemistableModel` $M_1$ for the $\mathrm{Fin}$-indexed telescope data $\mathcal{C}.\mathrm{teleFbar}$, $\mathcal{C}.\mathrm{teleChart}$, $\mathcal{C}.\mathrm{teleAn}$, $\mathcal{C}.\mathrm{teleSrc}$, $\mathcal{C}.\mathrm{teleTgt}$, $\mathcal{C}.\mathrm{teleXs}$, $\mathcal{C}.\mathrm{teleXt}$, obtained by composing with the enumerations $\mathcal{C}.\mathrm{eIdx}$ and $\mathcal{C}.\mathrm{eEdge}$, and a descent datum $D_1$ for $M_1$, such that $M_1.X = M.X$.
--
--   This is the reindexing step that converts a semistable model of the sum-indexed graph data of a full-level semistable covering into one for the same graph data indexed by $\mathrm{Fin}$ intervals, as used by the telescope formalism; the underlying scheme is unchanged. It is invoked by the statements producing the Tate-parameter maps and the vanishing on Igusa inertia for full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_SemistableCovering_exists_semistableModel_telescope.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

theorem ModularCurve.FullLevel.SemistableCovering.exists_semistableModel_telescope
    {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
    (𝒞 : SemistableCovering q M' A W)
    (M : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.sumFbar 𝒞.sumChart
      (fun e : CuspidalType.ProjLine q × ↥W => 𝒞.An e.1 e.2)
      (fun e => Sum.inl e.1) (fun e => Sum.inr e.2)
      (fun e => 𝒞.sumNode (Sum.inl e.1) e) (fun e => 𝒞.sumNode (Sum.inr e.2) e))
    (D : M.Descent) :
    ∃ (M₁ : AlgebraicCurve.SemistableModel A ↥(fieldBar q M') 𝒞.teleFbar 𝒞.teleChart 𝒞.teleAn 𝒞.teleSrc 𝒞.teleTgt
        𝒞.teleXs 𝒞.teleXt) (D₁ : M₁.Descent), M₁.X = M.X := by sorry
