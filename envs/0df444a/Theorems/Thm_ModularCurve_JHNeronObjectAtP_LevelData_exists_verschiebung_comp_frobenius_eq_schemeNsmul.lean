-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_verschiebung_comp_frobenius_eq_schemeNsmul
-- name    : ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/1dd32414-1440-58a5-b52b-295c62484342
-- title:
--   Verschiebung on the special fibre of the level-(M/p) abelian scheme
-- statement:
--   Fix a prime $p$ and a non-zero natural number $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, and level data $\Lambda$ of type `JHNeronObjectAtP.LevelData p M H hpM A`; of this data only the scheme $\Lambda.X$ with its structure morphism $\Lambda.f : \Lambda.X \to \operatorname{Spec}(\mathtt{baseRing }p)$ and the relative group law $\Lambda.L$ on $\Lambda.f$ enter the statement (a relative group law being a functorial multiplication, unit and inverse on points of $\Lambda.f$ over arbitrary base schemes, satisfying associativity, unit and inverse laws and compatible with base change of the parameter scheme). Assume $\Lambda.f$ carries the bundle `AbelianSchemePropertyBundle`, i.e. it is smooth and proper, has connected fibres, and admits some relative group law. Let $\sigma_p : \operatorname{Spec}(\mathbb{Z}/p) \to \mathtt{base }p$ be an $\mathbb{F}_p$-point of the base, write $\Lambda.X_{\sigma_p} \to \operatorname{Spec}(\mathbb{Z}/p)$ for the pullback `pullback.snd Λ.f σp` and $\Lambda.L.\mathrm{baseChange}\,\sigma_p$ for the induced group law on it. Let $F$ be an endomorphism of $\Lambda.X_{\sigma_p}$ over $\operatorname{Spec}(\mathbb{Z}/p)$ which is pinned to be the absolute Frobenius on affine points: for every commutative ring $B$ that is a $(\mathbb{Z}/p)$-algebra of characteristic $p$ and every point $x$ of $\Lambda.X_{\sigma_p}$ over $\operatorname{Spec}$ of the structure map $\mathbb{Z}/p \to B$, the composite $x$ followed by $F$ equals the $p$-power Frobenius of $B$ on spectra followed by $x$. Then there exists an endomorphism $V$ of $\Lambda.X_{\sigma_p}$ over $\operatorname{Spec}(\mathbb{Z}/p)$ such that $V$ followed by $F$ and $F$ followed by $V$ both equal the multiplication-by-$p$ morphism `schemeNsmul p` of $\Lambda.L.\mathrm{baseChange}\,\sigma_p$, and such that $V$ is a homomorphism for that group law: for every scheme $T$, every $s : T \to \operatorname{Spec}(\mathbb{Z}/p)$ and all points $x,y$ of $\Lambda.X_{\sigma_p}$ over $s$, the product of $x$ and $y$ followed by $V$ equals the product of ($x$ followed by $V$) and ($y$ followed by $V$).
--
--   This is the existence of the Verschiebung on the special fibre of the level-$(M/p)$ abelian scheme, together with the relations $VF = FV = [p]$ and the fact that $V$ respects the group law. It is consumed as data by the statements on Raynaud quotients and projector components for the $J_H$ Néron object, where $F$ and $V$ occur bound with exactly these pinning conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_verschiebung_comp_frobenius_eq_schemeNsmul.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.LevelData.exists_verschiebung_comp_frobenius_eq_schemeNsmul
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (F : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f))
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) (RelativeGroupLaw.baseChangeStr σp Λ.f)),
      (schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1) :
    ∃ V : SchemeHomOver (RelativeGroupLaw.baseChangeStr σp Λ.f) (RelativeGroupLaw.baseChangeStr σp Λ.f),
      V.1 ≫ F.1 = (Λ.L.baseChange σp).schemeNsmul p ∧ F.1 ≫ V.1 = (Λ.L.baseChange σp).schemeNsmul p ∧

      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp Λ.f)),
        schemeHomOverComp ((Λ.L.baseChange σp).mul s x y) V =
          (Λ.L.baseChange σp).mul s (schemeHomOverComp x V) (schemeHomOverComp y V)) := by sorry
