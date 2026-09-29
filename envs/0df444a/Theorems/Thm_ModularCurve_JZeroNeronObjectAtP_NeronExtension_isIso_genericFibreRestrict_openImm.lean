-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm
-- name    : ModularCurve.JZeroNeronObjectAtP.NeronExtension.isIso_genericFibreRestrict_openImm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/cd68836a-303c-54f5-b5c9-290a4a750603
-- title:
--   Generic fibre of the Néron extension open immersion is an isomorphism
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $p$ is a non-unit of $A$. Let $\Lambda$ be a `LevelData N₀ p A` (a structure morphism $\operatorname{Spec} A \to$ `base p` compatible with the generic point, together with a scheme over `base p` carrying a relative group law and bijections of its generic- and residue-point functors with $J_0(N_0)$-point sets), let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with structure morphism $O.g$ and relative group law $O.L$, and let $F$ be a Néron extension datum for $O$: a scheme $F.\mathrm{Nfull}$ with a morphism $F.gN$ to `shBase A`, a commutative relative group law over the valuation ring $\mathrm{shRing}\,A = A \cap K_A$ (the comap of $A$ along $K_A \hookrightarrow \overline{\mathbb Q}$, where $K_A = \mathrm{invField}\,A$ is the fixed field of the inertia subgroup of $A$ in $\overline{\mathbb Q}/\mathbb Q$), the Néron model property bundle $F.hN$ for $F.gN$ over $(\mathrm{shRing}\,A, K_A)$ under a Dedekind hypothesis, an open immersion $F.\mathrm{openImm}$ over `shBase A` from the base change $\mathrm{pullback.snd}\,O.g\,\Lambda.\mathrm{shStr}$ to $F.gN$, compatibility of this immersion with the group laws, surjectivity of its effect on points coming from $J_0(N_0p)$, and the component-group specialisation data. The assertion is that the induced morphism on generic fibres, namely the underlying scheme morphism of `genericFibreRestrict` for $F.\mathrm{openImm}$ — the map of pullbacks along $\operatorname{Spec}$ of $\mathrm{shRing}\,A \to K_A$ from $(\mathcal J \times_{\text{base}} \operatorname{Spec} \mathrm{shRing}\,A)_{K_A}$ to $(F.\mathrm{Nfull})_{K_A}$ — is an isomorphism.
--
--   This records that the identity component and the full Néron model of $J_0(N_0p)$ over the strict henselisation share the same generic fibre: the open immersion of the base-changed object into the Néron extension becomes an isomorphism after passing to the fraction field $K_A$. It is used in transporting Hecke endomorphisms and the Galois action to the Néron extension, via `exists_hecke_endomorphism` and `extN_galois_smul`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open AlgebraicGeometry

theorem ModularCurve.JZeroNeronObjectAtP.NeronExtension.isIso_genericFibreRestrict_openImm
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    IsIso (NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN
      (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) F.openImm).1 := by sorry
