-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData
-- name    : ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/6a40a4cc-d601-5c77-ad2b-793726a36e91
-- title:
--   Quasi-finiteness, quasi-compactness and flatness of [p^k] after base change
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H$ of $(\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a nonunit of $A$, with residue field of characteristic $p$ and algebraically closed. Let $\Lambda$ be a level datum for these data: it provides a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ (where the base ring is [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8)) compatible with the generic point, a scheme $X$ with a structure morphism $f \colon X \to \operatorname{Spec}\mathbb{Z}_{(p)}$, a relative group law $\Lambda.L$ on $f$, a bijection between $J_H$ at level $(M/p,\ \mathrm{infSubgroup}\ p\ M\ H\ hpM)$ and the sections of $f$ over the generic point, and a bijection $\Lambda.\mathrm{ptsSp}$ between $\mathrm{Pic}^0$ of the $q$-expansion function field `Fbar p M H hpM` over the residue field of $A$ and the sections of $f$ over the composite of the residue point with $\sigma_A$. Assume further that $f$ satisfies the abelian-scheme property bundle (smooth, proper, connected fibres, and admitting some relative group law), that $\Lambda.L$ is commutative on sections over every test base, and that $\Lambda.\mathrm{ptsSp}$ is additive. Then for every natural number $k$ the multiplication-by-$p^k$ endomorphism of the base change of $\Lambda.L$ along $\sigma_A$, namely `(Λ.L.baseChange Λ.σA).schemeNsmul (p ^ k)`, is locally quasi-finite, quasi-compact and flat.
--
--   This is the statement that multiplication by $p^k$ on an abelian scheme is a finite flat morphism, in the form needed over the local ring of $A$: the level abelian scheme attached to $J_H$ at a level exactly divisible by $p$ is base changed to $\operatorname{Spec} A$, and the isogeny $[p^k]$ on it retains quasi-finiteness, quasi-compactness and flatness. It is used in the rigidity step for the Néron object at $p$, where these three properties of $[p^k]$ are a hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_pow_baseChange_levelData
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛcomm : ∀ {T : Scheme.{0}} (t : T ⟶ base p) (x y : SchemeHomOver t Λ.f), Λ.L.mul t x y = Λ.L.mul t y x)
    (hadd : ∀ u v : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (u + v) = Λ.L.mul _ (Λ.ptsSp u) (Λ.ptsSp v))
    (k : ℕ) :
    LocallyQuasiFinite ((Λ.L.baseChange Λ.σA).schemeNsmul (p ^ k)) ∧
      QuasiCompact ((Λ.L.baseChange Λ.σA).schemeNsmul (p ^ k)) ∧ Flat ((Λ.L.baseChange Λ.σA).schemeNsmul (p ^ k)) := by sorry
