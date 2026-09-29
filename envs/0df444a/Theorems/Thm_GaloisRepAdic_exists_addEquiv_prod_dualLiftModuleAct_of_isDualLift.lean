-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
-- name    : GaloisRepAdic.exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/864729e9-3edd-58d9-ab2f-fe7669015656
-- title:
--   A framed first-order deformation is a dual-lift module
-- statement:
--   Let $k$ be a field and $p$ a prime. Let $\bar\rho$ be a residual representation over $k$, i.e. a $k$-vector space $\bar V$ of dimension $2$ together with a homomorphism $\bar\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_k(\bar V)$ factoring through a finite level, and let $\rho_A$ be a Galois representation over the dual numbers $k[\varepsilon]$: a free $k[\varepsilon]$-module $V_A$ of finite type with $\mathrm{rank} = 2$, a homomorphism $\rho_A \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_{k[\varepsilon]}(V_A)$, and the adic continuity condition that for each $n$ some finite subextension of $\mathbb Q$ in $\overline{\mathbb Q}$ has the property that its pointwise stabilisers act trivially modulo $\mathfrak m^n V_A$. Let $\rho_d \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \bigl((\mathrm{End}_k \bar V)[\varepsilon]\bigr)^\times$ be a homomorphism whose first component is $\bar\rho(g)$ for every $g$. Assume a framing: there are bases $b$ of $V_A$ over $k[\varepsilon]$ and $\bar b$ of $\bar V$, both indexed by $\mathrm{Fin}\,2$, such that for every $\sigma$ the matrix of $\rho_A(\sigma)$ in $b$ is the dual-number matrix assembled from the matrices in $\bar b$ of the two components of $\rho_d(\sigma)$. Finally let $c$ be a $1$-cocycle of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ valued in the subrepresentation of the adjoint representation on $\ker(\mathrm{tr}_k \colon \mathrm{End}_k \bar V \to k)$, and assume that $c(\sigma)$, viewed in $\mathrm{End}_k \bar V$, equals the second component of $\rho_d(\sigma)$ times $\bar\rho(\sigma)^{-1}$ for every $\sigma$. Then there is an additive isomorphism $\varphi \colon V_A \xrightarrow{\ \sim\ } \bar V \times \bar V$ such that for every $\sigma$ in $\mathrm{Gal}(\overline{\mathbb Q}_p/\mathbb Q_p)$, with image $g$ under the map to $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and every $x \in V_A$, writing $(v,w) = \varphi(x)$, one has $\varphi(\rho_A(g)x) = \bigl(\bar\rho(g)v,\ c(g)\bigl(\bar\rho(g)v\bigr) + \bar\rho(g)w\bigr)$; that is, $\varphi$ intertwines $\rho_A$ restricted to the decomposition group at $p$ with the dual-lift action of the restriction of $c$ along the local-to-global map (the image of $c$ under `mapCocycles₁` for the identity map on the restricted representation). The isomorphism $\varphi$ is asserted only additively, not $k[\varepsilon]$-linearly.
--
--   This is the dictionary between a framed first-order deformation of $\bar\rho$ over $k[\varepsilon]$ and the extension $\bar V \oplus \varepsilon \bar V$ determined by a trace-zero $1$-cocycle, in the form needed to compare the two models at the prime $p$. It is used in the study of the local condition at $p$ on the tangent space, where a bound on the invariants of a submodule of a first-order deformation is deduced from the corresponding bound for the dual-lift module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GaloisRep_LocalFlatClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology TrivSqZeroExt ExtCitation

theorem GaloisRepAdic.exists_addEquiv_prod_dualLiftModuleAct_of_isDualLift
    {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ρbar : ResidualGaloisRep k)
    (ρA : GaloisRepAdic (DualNumber k))
    (ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (DualNumber (Module.End k ρbar.V))ˣ)
    (hd : IsDualLift ρbar.ρ.toHomUnits ρd)
    (hframe : ∃ (b : Module.Basis (Fin 2) (DualNumber k) ρA.V) (bbar : Module.Basis (Fin 2) k ρbar.V),
      ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
        Matrix.dualNumberEquiv.symm
          ⟨LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).fst),
            LinearMap.toMatrix bbar bbar ((ρd σ : DualNumber (Module.End k ρbar.V)).snd)⟩)
    (c : cocycles₁ ρbar.adZero)
    (hc : ∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
        ↥(LinearMap.ker (LinearMap.trace k ρbar.V))) σ : Module.End k ρbar.V) =
      dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) :
    ∃ φ : ρA.V ≃+ ρbar.V × ρbar.V,
      ∀ (σ : primeLocalGaloisGroup (pPrime p)) (x : ρA.V),
        φ (ρA.ρ (primeLocalToGlobal (pPrime p) σ) x) =
          ρbar.dualLiftModuleAct p
            (mapCocycles₁ (primeLocalToGlobal (pPrime p))
              (𝟙 (Rep.res (primeLocalToGlobal (pPrime p)) ρbar.adZero)) c) σ (φ x) := by sorry
