-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
-- name    : NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/70b522ea-4bba-5243-baed-1dc92fb0772d
-- title:
--   Local invariant of the connecting map equals the Tate pairing
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes, an element $q \in S$ and an element $\zeta$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a primitive $p$-th root of unity. The assertion is the existence of a single unit $u \in (\mathbb{Z}/p)^{\times}$, depending only on $p$, $S$, $q$ and $\zeta$, such that the identity below holds for all of the following data.
--
--   *Coefficients and level.* A representation $M$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$) over $\mathbb{Z}/p$; an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is a number field and Galois over $\mathbb{Q}$; a height-one prime $w$ of $\mathcal{O}_F$. Throughout, $D_w$ denotes [`NumberField.PlaceDecomp.decomp ℚ F w`](def/NumberField_PlaceDecompositionAction.html#L82), the decomposition subgroup of $\mathrm{Gal}(F/\mathbb{Q})$ attached to the valuation subring of the $w$-adic valuation of $F$.
--
--   *$q$-adic coordinates at $w$ (five clauses).* An automorphism $\sigma$ of $\overline{\mathbb{Q}}$, a ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to `PadicAlgCl q` and a group homomorphism $\pi$ from `primeLocalGaloisGroup q` (the group of $\mathbb{Q}_q$-algebra automorphisms of `PadicAlgCl q`) to $D_w$, subject to: $\Phi(\iota_w(x)) = \mathrm{emb}_q(\sigma x)$ for all $x \in F$, where $\mathrm{emb}_q =$ [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is a fixed $\mathbb{Q}$-embedding of $\overline{\mathbb{Q}}$ into `PadicAlgCl q`; continuity of $\Phi$; for every $\tau$, the automorphism of $F$ underlying $\pi\tau$ is the restriction to $F$ of $\sigma^{-1} \cdot (\mathrm{primeLocalToGlobal}\ q)(\tau) \cdot \sigma$, where `primeLocalToGlobal` is the passage from local to global automorphisms through `PadicAlgCl q`; surjectivity of $\pi$; and $\Phi(\pi\tau \cdot x) = \tau(\Phi x)$ for all $\tau$ and all $x \in F_w$.
--
--   *The coefficient sequence and its Kummer pairing (eight clauses).* A short complex $T$ of $\mathbb{Z}$-linear representations of $\mathrm{Gal}(F/\mathbb{Q})$, assumed short exact (`hT`), and whose restriction along the inclusion of $D_w$ is also short exact (`hTD`); the requirement $p \cdot b = 0$ for all $b \in T.X_3$; a biadditive map $\kappa : T.X_3 \to M \to \mathrm{Additive}\,\overline{\mathbb{Q}}^{\times}$ which is equivariant in the sense that $\kappa(\rho_{T.X_3}(\gamma|_F) b,\ \rho_M(\gamma) m) = \gamma \cdot \kappa(b,m)$ for every automorphism $\gamma$ of $\overline{\mathbb{Q}}$, and perfect in the sense that every additive map $c : T.X_3 \to \mathrm{Additive}\,\overline{\mathbb{Q}}^{\times}$ is $\kappa(\cdot, m)$ for a unique $m \in M$; an additive map $\beta : T.X_3 \to M^{\vee}(\chi_p)$, where $M^{\vee}(\chi_p) =$ `M.dualTwist (cycloChar p)` is the $\mathbb{Z}/p$-dual of $M$ twisted by the mod $p$ cyclotomic character, such that $\kappa(b,m) = \zeta^{(\beta b)(m).\mathrm{val}}$ for all $b$ and $m$; and a biadditive $\kappa_q : T.X_3 \to M \to \mathrm{Additive}\,(\mathrm{PadicAlgCl}\ q)^{\times}$ which is the $\sigma$-transport of $\kappa$ along $\mathrm{emb}_q$, namely $\kappa_q(b,m) = \mathrm{emb}_q\bigl(\sigma \cdot \kappa(b, \rho_M(\sigma^{-1}) m)\bigr)$ on units.
--
--   *Idèlic data.* A descent datum $D$ of type `IdeleGaloisDescent (𝓞 F) ℚ F`, that is, a homomorphism from $\mathrm{Gal}(F/\mathbb{Q})$ to the ring automorphisms of the adèle ring of $F$, compatible with the structure map from $F$ and continuous in each component; a multiplicative-distributive action of $\mathrm{Gal}(F/\mathbb{Q})$ on the idèle class group $C_F = (\mathbb{A}_F)^{\times}/F^{\times}$, required to agree with the action `D.classAct` induced by $D$; a homomorphism $\iota$ from $F_w^{\times}$ to the idèle units whose $w$-component is the identity, whose components at all $w' \neq w$ are $1$ and whose infinite part is $1$; and a morphism of representations $\mathrm{lam}$ from the $D_w$-module $F_w^{\times}$ to the restriction to $D_w$ of the $\mathrm{Gal}(F/\mathbb{Q})$-module $C_F$, required to send $x$ to the class of $\iota x$.
--
--   *The local invariant (three clauses).* An additive map $\mathrm{inv}_{D_w} : H^2(D_w, C_F) \to \mathbb{Q}/\mathbb{Z} =$ `AddCircle (1 : ℚ)`, assumed injective, and normalised $p$-primarily as follows: for every finite-dimensional intermediate field $L'$ of $\mathrm{PadicAlgCl}\ q$ over $\mathbb{Q}_q$ carrying a $D_w$-semiring action and a compatible multiplicative-distributive action on $(L')^{\times}$, every ring isomorphism $\Phi' : F_w \xrightarrow{\sim} L'$ such that $D_w$ fixes $\mathbb{Q}_q$ inside $L'$, the action on $(L')^{\times}$ is induced by that on $L'$, and $\Phi'$ is $D_w$-equivariant; every finite-dimensional $K_0$ with `IsBase q L' D_w K₀`, i.e. $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$; every morphism $\theta'$ of $D_w$-representations from $(L')^{\times}$ to $F_w^{\times}$ given on units by $\Phi'^{-1}$; and every class $u' \in H^2(D_w, (L')^{\times})$ satisfying `IsLocalFundamentalClass q L' D_w K₀ u'` (the condition that $u'$ becomes, in every unramified overlay of $(L', D_w, K_0)$ as codified by `IsUnramOverlayerDatum`, the inflation of the cyclic carry class of a uniformiser): for all natural numbers $m$ and $a$ with $p$ coprime to $m$ and $m \cdot p^{a} = |D_w|$, one has $m \cdot \mathrm{inv}_{D_w}\bigl(\mathrm{lam}_*\theta'_*u'\bigr) = m/|D_w| \bmod \mathbb{Z}$.
--
--   *The local bridge and the local pairing (two clauses).* An additive map $\Lambda_q$ from the group of $D_w$-morphisms $T.X_1|_{D_w} \to F_w^{\times}$ to $H^1$ of the restriction of $M$ along `primeLocalToGlobal q`, subject to the predicate `IsLocalBridge₁` for the data $\pi$, the restrictions to $D_w$ of $T.f$ and $T.g$, the representation $F_w^{\times}$, the representation $(\mathrm{PadicAlgCl}\ q)^{\times}$ of the local group, the additive map induced by $\Phi$ on units, and $\kappa_q$; and a $\mathbb{Z}/p$-bilinear pairing $\theta_q$ on the continuous parts $\mathrm{continuousH}^1$ at the place $q$ (the image in $H^1$ of the level cocycles, for the homomorphism `extArithLoc S (Sum.inr q)`, which at an index $\mathrm{inr}\,q$ is `primeLocalToGlobal q`) of $M$ and of $M^{\vee}(\chi_p)$, subject to `IsTheta1` for the evaluation pairing $M \times M^{\vee}(\chi_p) \to$ `ofChar ((cycloChar p).comp (extArithLoc S (Sum.inr q)))` and for the functional `localInv p ζ q`: whenever $f$ and $g$ are level-constant $1$-cocycles and $e$ is a level $2$-cocycle equal to the cup cochain of $f$ and $g$, the value $\theta_q([f])([g])$ is the value of `localInv p ζ q` on the class of $e$.
--
--   *The classes compared.* A $D_w$-morphism $a_w : T.X_1|_{D_w} \to F_w^{\times}$; a $1$-cocycle $n$ of $\mathrm{Gal}(F/\mathbb{Q})$ with values in $T.X_3$; a $1$-cocycle $n_y$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with values in $M^{\vee}(\chi_p)$ satisfying $n_y(\gamma) = \beta(n(\gamma|_F))$ for all $\gamma$; an element $z_q$ of the continuous $H^1$ at $q$ of $M$ whose class in $H^1$ is $\Lambda_q(a_w)$; and an element $w_q$ of the continuous $H^1$ at $q$ of $M^{\vee}(\chi_p)$ whose class in $H^1$ is the localisation at the index $\mathrm{inr}\,q$ of the class of $n_y$.
--
--   Under these hypotheses the conclusion is the equality in $\mathbb{Q}/\mathbb{Z}$
--   $$\mathrm{inv}_{D_w}\Bigl( \bigl(a_w \text{ followed by } \mathrm{lam}\bigr)_*\, \delta_{hTD}\bigl( \mathrm{res}_{D_w}[n] \bigr) \Bigr) \;=\; \frac{\bigl(u \cdot \theta_q(z_q)(w_q)\bigr).\mathrm{val}}{p} \bmod \mathbb{Z},$$
--   where $\mathrm{res}_{D_w}[n]$ is the image of the class of $n$ in $H^1(\mathrm{Gal}(F/\mathbb{Q}), T.X_3)$ under the map induced in degree $1$ by the inclusion of $D_w$ and the identity of $T.X_3|_{D_w}$, $\delta_{hTD}$ is the connecting map of the $D_w$-restricted short exact sequence from degree $1$ to degree $2$, the outer arrow is the map induced in degree $2$ by the identity of $D_w$ and the composite morphism $a_w$ followed by $\mathrm{lam}$, and on the right $u \cdot \theta_q(z_q)(w_q)$ is the product in $\mathbb{Z}/p$ of the universal unit $u$ with the value of the local pairing, its canonical representative in $\{0, \dots, p-1\}$ being divided by $p$ in $\mathbb{Q}$ before reduction.
--
--   This is the place-by-place, $p$-primary form of the compatibility underlying Tate–Poitou duality: under the identifications of $\mathrm{Ext}^1$ groups used in the duality theorem, the map induced by the idèle group onto the idèle class group is computed at the place $q$ by the local Tate pairing, the discrepancy between the three independent normalisations (connecting map, local invariant, local pairing) being absorbed into one universal unit $u \in (\mathbb{Z}/p)^{\times}$. It feeds the construction of classes in the continuous Selmer group with prescribed localisations and the nondegeneracy of the resulting pairing between the first Shafarevich–Tate group of $M$ and the second one of $M^{\vee}(\chi_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge_primary.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_LocalInvariant
import Definitions.Def_GroupCohomology_LocalBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand ExtCitation
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge_primary
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

    (D : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F)
    [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)]
    (_ : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : IdeleClassGroup (𝓞 ↥F) ↥F), g • c = D.classAct g c)
    (ι : (w.adicCompletion ↥F)ˣ →* (AdeleRing (𝓞 ↥F) ↥F)ˣ)
    (_ : ∀ x : (w.adicCompletion ↥F)ˣ,
      finPart w (ι x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 ↥F), w' ≠ w → finPart w' (ι x) = 1) ∧ infPart (ι x) = 1)
    (lam : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F)))
    (_ : ∀ x : (w.adicCompletion ↥F)ˣ,
      lam.hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι x) : IdeleClassGroup (𝓞 ↥F) ↥F))

    (invD : ↥(groupCohomology (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype
        (Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (IdeleClassGroup (𝓞 ↥F) ↥F))) 2) →+ AddCircle (1 : ℚ))
    (_ : Function.Injective invD)
    (_ : ∀ (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ]
        (Φ' : w.adicCompletion ↥F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : w.adicCompletion ↥F), Φ' (g • x) = g • Φ' x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀)
        (θ' : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ ⟶ Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (w.adicCompletion ↥F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ'.hom (Additive.ofMul v)) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) = Φ'.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) K₀ u'),
        ∀ (m a : ℕ) (_ : p.Coprime m) (_ : m * p ^ a = Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)),
        m • invD
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) lam 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u')) =
          (((m : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M))
    (_ : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.f) ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (θq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M) →ₗ[ZMod p]
        Module.Dual (ZMod p) (continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))))
    (_ : IsTheta1 (extArithLoc S (Sum.inr q))
        (Module.Dual.eval (ZMod p) M :
          Rep.res (extArithLoc S (Sum.inr q)) M →ₗ[ZMod p]
            Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)) →ₗ[ZMod p]
              ofChar (k := ZMod p) ((cycloChar p).comp (extArithLoc S (Sum.inr q))))
        (localInv p ζ (q : Nat.Primes)) θq)

    (aw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (n : cocycles₁ T.X₃) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (_ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))
    (zq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) M))
    (_ : (zq : H1 (Rep.res (extArithLoc S (Sum.inr q)) M)) = Λq aw)
    (wq : continuousH1 (extArithLoc S (Sum.inr q)) (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p))))
    (_ : (wq : H1 (Rep.res (extArithLoc S (Sum.inr q)) (M.dualTwist (cycloChar p)))) = (locRes (extArithLoc S) (M.dualTwist (cycloChar p)) (Sum.inr q)).hom ((H1π (M.dualTwist (cycloChar p))).hom ny)),
    invD ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (aw ≫ lam) 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n))))
      = ((((((u : ZMod p) * θq zq wq).val : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by sorry
