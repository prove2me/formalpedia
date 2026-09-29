-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv
-- name    : NumberField.IdeleLocalInv.exists_transport_data_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/2c7788c8-127b-5260-a686-c913eba40009
-- title:
--   Transport data along an automorphism of a Galois layer
-- statement:
--   Let $E$ and $K$ be number fields with $K$ a Galois extension of $E$. Let $\sigma_K$ be a $\mathbb{Q}$-algebra automorphism of $K$ and $\tau$ a ring automorphism of $E$ with $\sigma_K(\iota x)=\iota(\tau x)$ for all $x\in E$, where $\iota\colon E\to K$ is the structure map; thus $\sigma_K$ normalises the base. Let $D$ be an `IdeleGaloisDescent` datum for $(\mathcal{O}_K,E,K)$, i.e. a monoid homomorphism $g\mapsto D.\mathrm{act}\,g$ from $\mathrm{Gal}(K/E)$ to the ring automorphisms of the adèle ring of $K$, each continuous and compatible with the action of $g$ on $K$ through the diagonal embedding; suppose moreover that the given multiplicative-distributive action of $\mathrm{Gal}(K/E)$ on the unit group of the adèle ring is the one induced by $D$ via `Units.mapEquiv`. Then there exist: a group automorphism $c$ of $\mathrm{Gal}(K/E)$; a self-map $\mathrm{pl}$ of the height-one spectrum of $\mathcal{O}_K$; a proof $h$ that $c$ carries the decomposition subgroup at $w$ (the decomposition subgroup in $\mathrm{Gal}(K/E)$ of the valuation subring of $w$) into the decomposition subgroup at $\mathrm{pl}\,w$; ring isomorphisms $T_c(w)\colon K_w\xrightarrow{\ \sim\ }K_{\mathrm{pl}\,w}$ of the adic completions; and a morphism $\psi$ of representations from the restriction along $c^{-1}$ of the unit group of the adèle ring (as a $\mathrm{Gal}(K/E)$-representation, written additively) to that same representation, such that: $c(g)(\sigma_K y)=\sigma_K(g y)$ for all $g$ and $y\in K$; the valuation at $\mathrm{pl}\,w$ of $\sigma_K y$ equals the valuation at $w$ of $y$; $\mathrm{pl}$ is bijective; $T_c(w)$ sends the image of $y\in K$ in $K_w$ to the image of $\sigma_K y$ in $K_{\mathrm{pl}\,w}$; $T_c(w)(g\cdot y)=c(g)\cdot T_c(w)(y)$ for $g$ in the decomposition subgroup at $w$; and for every idèle unit $z$, the $\mathrm{pl}\,w$-component `finPart` of $\psi(z)$ equals the image under $T_c(w)$ of the $w$-component `finPart` of $z$.
--
--   This packages, for the self-isomorphism of the layer $K/E$ given by the pair $(\tau,\sigma_K)$, the data needed to transport places, completions and idèles along an automorphism of a Galois layer: conjugation of the Galois group, the induced bijection of finite places, the induced isomorphisms of local fields, and the corresponding map on idèle units, each pinned by its values on $K$ and on components. It is used in the proof that the Brauer local invariant is unchanged by automorphisms of the layer ([`NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv`](thm.html#NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_exists_transport_data_of_algEquiv.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_IdeleLocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.exists_transport_data_of_algEquiv
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (σK : K ≃ₐ[ℚ] K) (τ : E ≃+* E) (hστ : ∀ x : E, σK (algebraMap E K x) = algebraMap E K (τ x))

    (D : IdeleGaloisDescent (𝓞 K) E K) [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (z : (AdeleRing (𝓞 K) K)ˣ), g • z = D.unitsAct g z) :
    ∃ (c : (K ≃ₐ[E] K) ≃* (K ≃ₐ[E] K))
      (pl : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 K))
      (hcd : ∀ (w : HeightOneSpectrum (𝓞 K)) (g : K ≃ₐ[E] K), g ∈ NumberField.PlaceDecomp.decomp E K w → c g ∈ NumberField.PlaceDecomp.decomp E K (pl w))
      (Tc : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ≃+* (pl w).adicCompletion K)
      (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ),

      (∀ (g : K ≃ₐ[E] K) (y : K), c g (σK y) = σK (g y)) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), (pl w).valuation K (σK y) = w.valuation K y) ∧
      Function.Bijective pl ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (y : K), Tc w (y : w.adicCompletion K) = ((σK y : K) : (pl w).adicCompletion K)) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K),
          Tc w (g • y) = (⟨c g, hcd w g g.2⟩ : ↥(NumberField.PlaceDecomp.decomp E K (pl w))) • Tc w y) ∧
      (∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ),
          finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion K →* (pl w).adicCompletion K) (finPart w z)) := by sorry
