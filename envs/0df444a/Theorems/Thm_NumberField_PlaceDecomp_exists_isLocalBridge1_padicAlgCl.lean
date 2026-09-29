-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl
-- name    : NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/43794f46-b5b7-50c8-9977-05974a564fcb
-- title:
--   Existence of a degree-one local bridge at a finite place
-- statement:
--   Fix a prime $p$ and a prime $q$, a representation $M$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ over $\mathbb Z/p$, and an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ which is a number field and Galois over $\mathbb Q$, together with a height-one prime $w$ of $\mathcal O_F$. The $q$-adic coordinates at $w$ consist of: an automorphism $\sigma$ of $\overline{\mathbb Q}$ over $\mathbb Q$; a continuous ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ into `PadicAlgCl q` with $\Phi(x)=\mathrm{padicEmbedding}(\sigma x)$ for $x\in F$; a group homomorphism $\pi$ from `primeLocalGaloisGroup q` $=\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)$ to the decomposition subgroup `decomp ℚ F w` of $w$ in $\mathrm{Gal}(F/\mathbb Q)$, given by $\tau\mapsto(\sigma^{-1}\,\mathrm{primeLocalToGlobal}(\tau)\,\sigma)|_F$, assumed surjective, with $\Phi(\pi(\tau)\cdot x)=\tau(\Phi x)$ for all $x\in F_w$. Further data: morphisms $R\xrightarrow{f}P\xrightarrow{g}B$ of representations of $\mathrm{Gal}(F/\mathbb Q)$ over $\mathbb Z$ with $f$ injective, $f,g$ exact and $g$ surjective, an isomorphism of $P$ with the free representation on a finite type $\alpha$, $pB=0$, and a biadditive $\kappa : B \to M \to \mathrm{Additive}\,(\mathrm{PadicAlgCl}\,q)^{\times}$ which is equivariant for $\pi$ and `primeLocalToGlobal q` against the Galois action on units, and perfect in $M$: every additive $c : B\to \mathrm{Additive}\,(\mathrm{PadicAlgCl}\,q)^{\times}$ equals $\kappa(\cdot\,,m)$ for a unique $m\in M$. The conclusion asserts the existence of an additive map $\Lambda$ from the group of morphisms of representations of `decomp ℚ F w` from $R$ restricted along the subgroup inclusion to $F_w^{\times}$ (with its multiplicative action) into $H^1$ of $M$ restricted along `primeLocalToGlobal q`, such that: $\Lambda$ satisfies the predicate `IsLocalBridge₁` for $\pi$, the restrictions of $f$ and $g$, $X=F_w^{\times}$, $A=(\mathrm{PadicAlgCl}\,q)^{\times}$ with its Galois action, the additivisation of $\mathrm{Units.map}\,\Phi$, and $\kappa$; $\Lambda\varphi=0$ holds exactly when $\varphi$ factors as $f$ followed by some $\chi : P\to F_w^{\times}$; and the image of $\Lambda$ is precisely the submodule `continuousH1` of $H^1$ attached to `primeLocalToGlobal q`, namely the image of `levelCocycles₁` under the projection to $H^1$.
--
--   This is the local term at the finite place $q$ in the degree-one Tate-duality comparison: it realises $\mathrm{Ext}^1_{D_w}(B,F_w^{\times})$, presented as a bridge map out of $\mathrm{Hom}_{D_w}(R,F_w^{\times})$, as $H^1_{\mathrm{cts}}(\mathbb Q_q,M)$, at every finite Galois level at which the pairing $\kappa$ is perfect. It feeds the assembly of the idèle term of the Poitou–Tate rows, being cited by [`groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two`](thm.html#groupCohomology.exists_mem_continuousH1S_locRes_eq_of_forall_sum_theta_eq_zero_arch_of_ne_two) and [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_isLocalBridge1_padicAlgCl.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp NumberField.InfPlaceDecomp

theorem NumberField.PlaceDecomp.exists_isLocalBridge1_padicAlgCl
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (hπsurj : Function.Surjective π)
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    (α : Type) [Finite α] (eP : P ≅ Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) α) (hB : ∀ b : B, p • b = 0)
    (κ : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκeq : ∀ (τ : primeLocalGaloisGroup q) (b : B) (m : M),
      κ (B.ρ ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (primeLocalToGlobal q τ) m) =
        (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (κ b m))
    (hκ : ∀ c : B →+ Additive (PadicAlgCl q)ˣ, ∃! m : M, ∀ b, κ b m = c b) :
    ∃ Λ : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M),
      IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κ Λ ∧
      (∀ φ, Λ φ = 0 ↔ ∃ χ : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype P ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ,
        (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f ≫ χ = φ) ∧
      (∀ φ, Λ φ ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) ∧
      (∀ y ∈ continuousH1 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M), ∃ φ, Λ φ = y) := by sorry
