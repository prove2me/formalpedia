-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge
-- name    : NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/075b9732-73ad-54c6-b24c-bfc1ff625d00
-- title:
--   Idèle-class invariant at w equals the local Tate pairing
-- statement:
--   Fix a prime $p$, a finite set $S$ of primes, an element $q \in S$, and an element $\zeta$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a primitive $p$-th root of unity. The assertion is the existence of a single unit $u \in (\mathbb{Z}/p)^{\times}$, depending on these data only, such that for every configuration of the objects listed below the displayed identity in $\mathbb{Q}/\mathbb{Z} =$ `AddCircle (1 : ℚ)` holds.
--
--   *Representation and level.* A representation $M$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$, an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is a number field and Galois over $\mathbb{Q}$, and a height-one prime $w$ of $\mathcal{O}_F$. Throughout, [`NumberField.PlaceDecomp.decomp ℚ ↥F w`](def/NumberField_PlaceDecompositionAction.html#L82) denotes the decomposition subgroup of $\mathrm{Gal}(F/\mathbb{Q})$ attached to the valuation subring of the $w$-adic valuation of $F$, written $D_w$ below, and `primeLocalGaloisGroup q` denotes $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ for the chosen algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, with `primeLocalToGlobal q` the homomorphism to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting scalars to $\mathbb{Q}$ and then restricting to $\overline{\mathbb{Q}}$.
--
--   *$q$-adic coordinates at $w$ (four hypotheses).* An element $\sigma$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, a ring homomorphism $\Phi$ from the $w$-adic completion $F_w$ to $\overline{\mathbb{Q}}_q$, and a group homomorphism $\pi : \mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q) \to D_w$, subject to: $\Phi(\iota_w(x)) = \mathrm{padicEmbedding}_q(\sigma x)$ for all $x \in F$, where $\iota_w$ is the structure map $F \to F_w$ and [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) is a fixed embedding $\overline{\mathbb{Q}} \to \overline{\mathbb{Q}}_q$; $\Phi$ is continuous; for every $\tau$ the element $\pi(\tau)$, viewed in $F \simeq_{\mathbb{Q}} F$, is the restriction to $F$ of $\sigma^{-1}\,(\mathrm{primeLocalToGlobal}_q\,\tau)\,\sigma$; $\pi$ is surjective; and $\Phi(\pi(\tau) \cdot x) = \tau(\Phi x)$ for all $\tau$ and all $x \in F_w$.
--
--   *Short exact sequence and Kummer pairings (eight hypotheses).* A short complex $T$ of representations of $\mathrm{Gal}(F/\mathbb{Q})$ over $\mathbb{Z}$, short exact (`hT`), whose restriction along the inclusion $D_w \hookrightarrow \mathrm{Gal}(F/\mathbb{Q})$ is again short exact (`hTD`); every $b \in T.X_3$ satisfies $p \cdot b = 0$; a biadditive pairing $\kappa : T.X_3 \to (M \to \mathrm{Additive}\,\overline{\mathbb{Q}}^{\times})$ which is equivariant in the sense that $\kappa(\rho_{T.X_3}(\gamma|_F)\,b)(\rho_M(\gamma)\,m) = \gamma \cdot \kappa(b)(m)$ for all $\gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the action on $\overline{\mathbb{Q}}^{\times}$ being `Rep.ofAlgebraAutOnUnits`, and which is perfect on the $M$-side: every additive map $c : T.X_3 \to \mathrm{Additive}\,\overline{\mathbb{Q}}^{\times}$ is $\kappa(\cdot)(m)$ for a unique $m \in M$. An additive map $\beta : T.X_3 \to M^{\vee}(\mathrm{cycloChar}\,p)$, the $\mathbb{Z}/p$-dual of $M$ with action twisted by the mod-$p$ cyclotomic character, such that $\kappa(b)(m) = \zeta^{\,(\beta b)(m).\mathrm{val}}$ in $\overline{\mathbb{Q}}$ for all $b, m$. A second biadditive pairing $\kappa_q : T.X_3 \to (M \to \mathrm{Additive}\,\overline{\mathbb{Q}}_q^{\times})$ given by the $\sigma$-transport of $\kappa$: $\kappa_q(b)(m)$ is the image under [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) of $\sigma \cdot \kappa(b)(\rho_M(\sigma^{-1})m)$.
--
--   *Idèle-theoretic data (four hypotheses).* A descent datum $D$ of type `IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F`, that is, a homomorphism from $\mathrm{Gal}(F/\mathbb{Q})$ to the ring automorphisms of the adèle ring of $F$, compatible with the structure map from $F$ and continuous in each automorphism; a multiplicative action of $\mathrm{Gal}(F/\mathbb{Q})$ on the idèle class group $C_F = (\mathbb{A}_F)^{\times}/F^{\times}$ pinned to coincide with `D.classAct`; a homomorphism $\iota : F_w^{\times} \to (\mathbb{A}_F)^{\times}$ whose $w$-component is the identity, whose components at all finite places $w' \ne w$ are $1$ and whose infinite part is $1$; and a morphism $\mathrm{lam}$ of representations of $D_w$ from $F_w^{\times}$ to the restriction of $C_F$ along $D_w \hookrightarrow \mathrm{Gal}(F/\mathbb{Q})$, pinned to send $x$ to the class of $\iota(x)$.
--
--   *The local invariant (two hypotheses).* An additive map $\mathrm{inv}_{D_w}$ from $H^2(D_w, C_F|_{D_w})$ to $\mathbb{Q}/\mathbb{Z}$ which is injective, and which is normalised as follows: for every finite extension $L'$ of $\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ carrying a multiplicative semiring action of $D_w$ and a multiplicative action on $(L')^{\times}$, every ring isomorphism $\Phi' : F_w \to L'$, subject to $D_w$ acting $\mathbb{Q}_q$-linearly on $L'$, the action on $(L')^{\times}$ being induced by the action on $L'$, and $\Phi'$ being $D_w$-equivariant, every finite extension $K_0$ of $\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ with [`ExtCitation.LocalLevel.IsBase q L' D_w K₀`](def/ExtCitation_LocalLevel_FundamentalClass.html#L13), i.e. $K_0 \le L'$ and an element of $L'$ lies in $K_0$ exactly when it is fixed by all of $D_w$, every morphism $\theta'$ of $D_w$-representations from $(L')^{\times}$ to $F_w^{\times}$ inducing $(\Phi')^{-1}$ on coefficients, and every class $u' \in H^2(D_w, (L')^{\times})$ satisfying [`ExtCitation.LocalLevel.IsLocalFundamentalClass q L' D_w K₀ u'`](def/ExtCitation_LocalLevel_FundamentalClass.html#L60) — the condition that on every finite overlay $L' \subseteq M'$ equipped with a finite faithful group $H$, normal subgroups $N_L, N_n \trianglelefteq H$, an isomorphism $D_w \simeq H/N_L$, a Frobenius element $\varphi$ and a uniformiser $\pi_0$ forming an `IsUnramOverlayerDatum`, the pull-back of $u'$ is the inflation of the class of the cyclic carry $2$-cocycle built from $\varphi$ and $\pi_0$ — one has
--   $$\mathrm{inv}_{D_w}\bigl(\mathrm{lam}_*\,\theta'_*\,u'\bigr) = \frac{1}{\#D_w} \bmod \mathbb{Z},$$
--   the push-forwards being `groupCohomology.map` in degree $2$ along the identity of $D_w$.
--
--   *Local bridge and local Tate pairing (two hypotheses).* An additive map $\Lambda_q$ from the group of morphisms of $D_w$-representations $T.X_1|_{D_w} \to F_w^{\times}$ to $H^1(\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q), M|_{\mathbb{Q}_q})$, required to satisfy the predicate `IsLocalBridge₁` for the data: $\pi$, the restrictions along $D_w \hookrightarrow \mathrm{Gal}(F/\mathbb{Q})$ of the two maps $T.f$ and $T.g$ of $T$, the representation of $D_w$ on $F_w^{\times}$ as ambient object $X$, the representation `Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)` of $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ on $\overline{\mathbb{Q}}_q^{\times}$ as $A$, the additive map induced by `Units.map Φ`, the restriction of $M$ along `primeLocalToGlobal q`, and the pairing $\kappa_q$; this predicate pins $\Lambda_q$ as the Kummer-type bridge attached to $\Phi$ and $\kappa_q$. A $\mathbb{Z}/p$-linear map $\theta_q$ from the continuous part of $H^1$ of $M$ restricted along `extArithLoc S (Sum.inr q)` (which is `primeLocalToGlobal q`) to the $\mathbb{Z}/p$-dual of the continuous part of $H^1$ of $M^{\vee}(\mathrm{cycloChar}\,p)$ restricted along the same map, where the continuous part is the image in $H^1$ of the level cocycles; $\theta_q$ is required to satisfy `IsTheta1` for the evaluation pairing $M \times M^{\vee}(\chi) \to \mathrm{ofChar}(\chi \circ \mathrm{primeLocalToGlobal}\,q)$, with $\chi = \mathrm{cycloChar}\,p$, and for the functional `localInv p ζ q`: that is, whenever $f$ and $g$ are level-constant $1$-cocycles with values in $M$ and in $M^{\vee}(\chi)$ and $e$ is a level $2$-cocycle whose values agree pointwise with the cup cochain of $f$ and $g$ under the evaluation pairing, then $\theta_q([f])([g])$ equals the value of `localInv p ζ q` on the class of $e$ in the continuous $H^2$.
--
--   *The classes whose invariant is computed (four hypotheses).* A morphism $a_w$ of $D_w$-representations from $T.X_1|_{D_w}$ to $F_w^{\times}$; a $1$-cocycle $n$ of $\mathrm{Gal}(F/\mathbb{Q})$ with values in $T.X_3$; a $1$-cocycle $n_y$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with values in $M^{\vee}(\mathrm{cycloChar}\,p)$ such that $n_y(\gamma) = \beta\bigl(n(\gamma|_F)\bigr)$ for all $\gamma$; an element $z_q$ of the continuous $H^1$ of $M|_{\mathbb{Q}_q}$ whose underlying class equals $\Lambda_q(a_w)$; and an element $w_q$ of the continuous $H^1$ of $M^{\vee}(\mathrm{cycloChar}\,p)|_{\mathbb{Q}_q}$ whose underlying class is the localisation at $\mathrm{Sum.inr}\,q$, via `locRes (extArithLoc S)`, of the class of $n_y$ in $H^1(\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}), M^{\vee}(\mathrm{cycloChar}\,p))$.
--
--   *Conclusion.* Let $[n] \in H^1(\mathrm{Gal}(F/\mathbb{Q}), T.X_3)$ be the class of $n$, let $\mathrm{res}\,[n] \in H^1(D_w, T.X_3|_{D_w})$ be its image under `groupCohomology.map` along the inclusion $D_w \hookrightarrow \mathrm{Gal}(F/\mathbb{Q})$ with the identity of $T.X_3|_{D_w}$, let $\delta$ be the connecting map $H^1(D_w, T.X_3|_{D_w}) \to H^2(D_w, T.X_1|_{D_w})$ of the short exact sequence `hTD`, and let $(a_w \text{ followed by } \mathrm{lam})_*$ be the degree-$2$ push-forward along the identity of $D_w$ and the composite of $a_w$ with $\mathrm{lam}$. Then
--   $$\mathrm{inv}_{D_w}\Bigl((a_w \text{ followed by } \mathrm{lam})_*\,\delta\,\mathrm{res}\,[n]\Bigr) = \frac{\bigl(u \cdot \theta_q(z_q)(w_q)\bigr).\mathrm{val}}{p} \bmod \mathbb{Z},$$
--   where $u \cdot \theta_q(z_q)(w_q)$ is computed in $\mathbb{Z}/p$, its canonical representative in $\{0,\dots,p-1\}$ is taken, divided by $p$ in $\mathbb{Q}$ and reduced in $\mathbb{Q}/\mathbb{Z}$.
--
--   This is the place-by-place local ingredient in the comparison, under Tate duality, of the idèle-class invariant of a degree-two class obtained from a connecting map with the local Tate pairing at a finite place $q$: the left-hand side reads the class $\delta[n]$, pushed into the idèle class group through the local component at $w$, against the normalised invariant $\mathrm{inv}_{D_w}$, and the right-hand side is the cup-product pairing $\theta_q$ of the corresponding local classes, up to one unit $u \in (\mathbb{Z}/p)^{\times}$ that is uniform in all the data and absorbs the orientation conventions of the connecting map, the local invariant and the Kummer pairing. It is used in the proof of the non-degeneracy of the pairing between the first Tate–Shafarevich group of $M$ and the second of its twisted dual, [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_unit_inv_map_delta_res_eq_theta_localBridge.lean

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

theorem NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge
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
        invD ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) lam 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) θ' 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

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
