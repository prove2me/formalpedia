-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
-- name    : NumberField.PlaceDecomp.exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/6f25aa48-9747-5ea9-986c-3235cdf6f878
-- title:
--   Local bridge matches δ with a cup product up to a unit
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes, a member $q$ of $S$, and a primitive $p$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$. The assertion is that there is a unit $u \in (\mathbb{Z}/p)^{\times}$, depending on nothing else, such that the following holds for all data of the following kind. A representation $M$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$; a finite Galois subextension $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and a height-one prime $w$ of $\mathcal{O}_F$; $q$-adic coordinates at $w$, namely $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, a continuous ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to $\overline{\mathbb{Q}}_q$ agreeing on $F$ with $\iota_q \circ \sigma$ (where $\iota_q$ is the fixed embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$), and a surjective homomorphism $\pi$ from $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ onto the decomposition subgroup $D_w \le \mathrm{Gal}(F/\mathbb{Q})$ attached to the valuation subring of $w$, with $\pi\tau$ the restriction to $F$ of $\sigma^{-1}\,\mathrm{loc}_q(\tau)\,\sigma$ and $\Phi$ $\pi$-semilinear, where $\mathrm{loc}_q$ is the map from $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to $\overline{\mathbb{Q}}$. Further, a short complex $T$ of $\mathbb{Z}[\mathrm{Gal}(F/\mathbb{Q})]$-modules that is short exact and remains short exact after restriction to $D_w$, with $T.X_3$ killed by $p$; a biadditive pairing $\kappa$ of $T.X_3$ with $M$ into $\overline{\mathbb{Q}}^{\times}$ (written additively) that is equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting on $T.X_3$ through restriction to $F$, and perfect in the sense that every additive map $T.X_3 \to \overline{\mathbb{Q}}^{\times}$ is $\kappa(\cdot, m)$ for exactly one $m \in M$; its $\zeta$-logarithm $\beta$, an additive map from $T.X_3$ to the dual of $M$ twisted by the mod $p$ cyclotomic character, with $\kappa(b,m) = \zeta^{(\beta b)(m).\mathrm{val}}$; and the transport $\kappa_q$ of $\kappa$ into $\overline{\mathbb{Q}}_q^{\times}$ along $\sigma$ and $\iota_q$. Finally an additive map $\Lambda_q$ from $D_w$-equivariant maps $T.X_1 \to F_w^{\times}$ to $H^1$ of $M$ restricted along $\mathrm{loc}_q$, assumed to satisfy the predicate `IsLocalBridge₁` relative to $\pi$, the restrictions of $T.f$ and $T.g$, the map induced by $\Phi$ on units, and $\kappa_q$; an equivariant $a_w : T.X_1 \to F_w^{\times}$ over $D_w$; $1$-cocycles $n$ valued in $T.X_3$ and $ny$ valued in the twisted dual of $M$ with $ny(\gamma) = \beta(n(\gamma|_F))$; a $1$-cocycle $f_q$ of $M$ over the local group representing $\Lambda_q(a_w)$ and satisfying `IsLevelConstant₁` along $\mathrm{loc}_q$; the $1$-cocycle $g_q$ given by $ny \circ \mathrm{loc}_q$; a level $2$-cocycle $e$ valued in $\mathbb{Z}/p$ twisted by the cyclotomic character composed with $\mathrm{loc}_q$, equal as a function to the cup cochain $(g,h) \mapsto \langle f_q(g), \rho(g) g_q(h)\rangle$ for the evaluation pairing; the level $2$-cocycle $E$ with $E(g,h) = \iota_q(\zeta)^{e(g,h).\mathrm{val}}$ in $\overline{\mathbb{Q}}_q^{\times}$; a $2$-cocycle $x$ valued in $F_w^{\times}$ whose class is the image under $a_w$ of the connecting map in degree $1 \to 2$ applied to the restriction to $D_w$ of the class of $n$; and the level $2$-cocycle $X$ with $X(g,h) = \Phi(x(\pi g, \pi h))$. The conclusion is that in the continuous $H^2$ of $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ with values in $\overline{\mathbb{Q}}_q^{\times}$ — the quotient of level $2$-cocycles by the level coboundaries among them — the class of $X$ equals $u.\mathrm{val}$ times the class of $E$.
--
--   This is the local half of the place-by-place comparison: at a place $w$ of $F$ above $q$, the connecting map of the chosen presentation followed by $a_w$ agrees, in $q$-adic coordinates and up to one universal unit of $\mathbb{Z}/p$, with the cup product of the bridge class $\Lambda_q(a_w)$ with the localisation of the $\beta$-avatar of the class of $n$. It is used by the two statements that package this identity in terms of the local bridge and the form $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : (ZMod p)ˣ,
    ∀ (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))

    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (_ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (_ : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (_ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (_ : Function.Surjective π)
    (_ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

    (T : ShortComplex (Rep ℤ (↥F ≃ₐ[ℚ] ↥F))) (hT : T.ShortExact)
    (hTD : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).ShortExact)
    (_ : ∀ b : T.X₃, p • b = 0)
    (κ : T.X₃ →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (_ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : T.X₃) (m : M),
      κ (T.X₃.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (_ : ∀ c : T.X₃ →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (β : T.X₃ →+ M.dualTwist (cycloChar p))
    (_ : ∀ (b : T.X₃) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)
    (κq : T.X₃ →+ M →+ Additive (PadicAlgCl q)ˣ)
    (_ : ∀ (b : T.X₃) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))

    (Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M))
    (_ : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.f) ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)

    (aw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (n : cocycles₁ T.X₃) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (_ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))

    (fq : cocycles₁ (Rep.res (primeLocalToGlobal q) M)) (_ : (H1π _).hom fq = Λq aw)
    (hfq : IsLevelConstant₁ (primeLocalToGlobal q) (⇑fq))
    (gq : cocycles₁ (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))))
    (_ : ∀ τ : primeLocalGaloisGroup q, gq τ = ny (primeLocalToGlobal q τ))
    (e : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (_ : ∀ st, (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) st =
      cupCochain (Module.Dual.eval (ZMod p) M :
          Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p]
            Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p] (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
        (⇑fq) (⇑gq) st)

    (E : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, ((Additive.toMul ((E : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h) : ZMod p).val))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))
    (_ : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) aw 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n))))
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h)))),
    continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) X =
      (((u : ZMod p).val : ℤ)) • continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) E := by sorry
