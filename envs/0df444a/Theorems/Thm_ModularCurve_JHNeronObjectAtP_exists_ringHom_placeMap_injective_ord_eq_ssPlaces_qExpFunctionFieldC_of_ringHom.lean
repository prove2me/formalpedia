-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
-- name    : ModularCurve.JHNeronObjectAtP.exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/b907f935-7878-5645-a6a4-0ff091b81f88
-- title:
--   Transport of q-expansion fields and places along κ(P)→ K
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime, $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$ and a divisibility $p \mid M$; let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ whose residue field $\kappa := \kappa(Pl)$ is algebraically closed of characteristic $p$, let $K$ be an algebraically closed field of characteristic $p$, and let $\iota \colon \kappa \to K$ be a ring homomorphism. Write $\Gamma' =$ [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $(M/p)$ applied to the image of $H$ in $(\mathbb{Z}/(M/p))^\times$ under reduction, namely the image in $SL_2(\mathbb{Z})$ of the pullback of that image along `gamma0Units`; this is the level group occurring in [`ModularCurve.JHNeronObjectAtP.Fbar p M H hpM κ`](def/ModularCurve_JHNeronObjectAtP.html#L29), the intermediate field `qExpFunctionFieldC κ Γ'` of $\kappa((q))$ obtained by adjoining to $\kappa$ the integral-form ratios of level $\Gamma'$. The assertion is the existence of a ring homomorphism $e_K$ from that field to `qExpFunctionFieldC K Γ'` and of a map $\pi$ from places of the former over $\kappa$ (valuation subrings containing $\kappa$, proper, and principal ideal rings) to places of the latter over $K$, such that: $e_K(g)$ is the Laurent series obtained from $g$ by applying $\iota$ to all coefficients; $\operatorname{ord}_{\pi(v)} e_K(g) = \operatorname{ord}_v g$ for all $g$ and $v$; every place in `ssPlacesQExp K Γ' p` lies in the range of $\pi$; $\pi$ is injective; $\operatorname{ord}_V e_K(g) = 0$ for every $V$ outside the range of $\pi$; and $\pi(v)$ lies in `ssPlacesQExp K Γ' p` if and only if $v$ lies in `ssPlacesQExp κ Γ' p`.
--
--   This is the constant-field-extension comparison for the $q$-expansion function field of $\Gamma_{H'}(M/p)$: a prescribed embedding of the residue field of a place of $\overline{\mathbb{Q}}$ above $p$ into an algebraically closed field $K$ is lifted to the function fields, matching orders at places, capturing all supersingular places of the larger field in the image, and detecting supersingularity on both sides. It feeds the construction of reduced root functions with prescribed divisibility of orders used in the Abel–Jacobi analysis of $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JHNeronObjectAtP.exists_ringHom_placeMap_injective_ord_eq_ssPlaces_qExpFunctionFieldC_of_ringHom
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (ι : IsLocalRing.ResidueField ↥Pl →+* K) :
    ∃ (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl) →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
      (plK : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl), ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ι (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl))) ∧
      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), (plK v).ord (eK g) = v.ord g) ∧

      (∀ V : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
        V ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p →
          ∃ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)), plK v = V) ∧
      Function.Injective plK ∧

      (∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (V : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
        V ∉ Set.range plK → V.ord (eK g) = 0) ∧
      (∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
        plK v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p ↔
          v ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) := by sorry
