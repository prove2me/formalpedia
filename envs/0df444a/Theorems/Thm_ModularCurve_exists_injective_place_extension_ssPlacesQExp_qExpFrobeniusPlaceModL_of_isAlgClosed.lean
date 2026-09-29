-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
-- name    : ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/b272ebcf-2473-5532-adad-057c1281c3a4
-- title:
--   Constant field extension of places of the q-expansion curve
-- statement:
--   Let $p$ be a prime and let $\kappa \subseteq K$ be algebraically closed fields of characteristic $p$, with $K$ a $\kappa$-algebra, and let $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$. Write $F_\kappa =$ [`ModularCurve.qExpFunctionFieldC κ Γ`](def/ModularCurve_X1.html#L101) for the subfield of $\kappa((q))$ generated over $\kappa$ by the quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of reductions of integral $q$-expansions of modular forms of some weight for $\Gamma$, and similarly $F_K \subseteq K((q))$. Assume each of $F_\kappa/\kappa$ and $F_K/K$ satisfies [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (principal divisors of degree zero exist for every nonzero function, every place has residue field finite over the constant field, and the module of Kähler differentials is free of rank one), and that each is finitely generated in the sense that it contains a transcendental element over which it is finite-dimensional. Let $\iota\colon F_\kappa \to F_K$ be a ring homomorphism which on Laurent series is the coefficientwise application of $\kappa \to K$. Then there is a map $\mathrm{ext}$ from places of $F_\kappa/\kappa$ to places of $F_K/K$ — a place being a valuation subring containing the constant field, not equal to the whole field, and a principal ideal ring — such that: $\mathrm{ext}$ is injective; $f \in \mathcal{O}_v \iff \iota f \in \mathcal{O}_{\mathrm{ext}(v)}$; any $w$ with $\mathcal{O}_v = \iota^{-1}\mathcal{O}_w$ equals $\mathrm{ext}(v)$; every $w$ with $\iota^{-1}\mathcal{O}_w \ne F_\kappa$ lies in the image of $\mathrm{ext}$; $\mathrm{ord}_{\mathrm{ext}(v)}(\iota f) = \mathrm{ord}_v(f)$; $v$ takes the value $a \in \kappa$ at $f$ (i.e. $f \in \mathcal{O}_v$ with residue the image of $a$) if and only if $\mathrm{ext}(v)$ takes the value $\mathrm{algebraMap}\,\kappa\,K\,(a)$ at $\iota f$; $v$ lies in [`ModularCurve.ssPlacesQExp κ Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27) (some $x \in F_\kappa$ with Laurent series $\mathrm{jqModC}\,\kappa$ has a value at $v$ lying in the supersingular set $\mathrm{ssJSet}_p$) if and only if $\mathrm{ext}(v)$ lies in [`ModularCurve.ssPlacesQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27); every supersingular place of $F_K/K$ is in the image of $\mathrm{ext}$; and $\mathrm{ext}$ commutes with the place map induced by the $q$-expansion Frobenius in characteristic $p$, namely $\mathrm{ext}(\mathrm{qExpFrobeniusPlaceModL}_\kappa(v)) = \mathrm{qExpFrobeniusPlaceModL}_K(\mathrm{ext}(v))$.
--
--   This is the constant field extension of places for the function field of the modular curve attached to $\Gamma$, in the form needed when one enlarges the algebraically closed field of constants from, say, $\overline{\mathbb{F}}_p$ to a larger algebraically closed field: closed points base change uniquely, orders and values are preserved, and both supersingularity and the Frobenius action on places are compatible with the extension. It is used in the comparison of the $q$-expansion curve with its Néron-type model at $p$ and in the analysis of the diamond operators together with Frobenius on supersingular places mod $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
    (p : ℕ) [Fact p.Prime]
    (κ K : Type*) [Field κ] [Field K] [IsAlgClosed κ] [IsAlgClosed K] [CharP κ p] [CharP K p] [Algebra κ K]
    (Γ : Subgroup SL(2, ℤ))
    [AlgebraicCurve.IsCurveOver κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)]
    [AlgebraicCurve.IsCurveOver K ↥(ModularCurve.qExpFunctionFieldC K Γ)]
    (hfgκ : ∃ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), Transcendental κ x ∧
      FiniteDimensional ↥(IntermediateField.adjoin κ ({x} : Set ↥(ModularCurve.qExpFunctionFieldC κ Γ))) ↥(ModularCurve.qExpFunctionFieldC κ Γ))
    (hfgK : ∃ x : ↥(ModularCurve.qExpFunctionFieldC K Γ), Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set ↥(ModularCurve.qExpFunctionFieldC K Γ))) ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (ι : ↥(ModularCurve.qExpFunctionFieldC κ Γ) →+* ↥(ModularCurve.qExpFunctionFieldC K Γ))
    (hι : ∀ x : ↥(ModularCurve.qExpFunctionFieldC κ Γ), ((ι x : ↥(ModularCurve.qExpFunctionFieldC K Γ)) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap κ K) (x : LaurentSeries κ)) :
    ∃ ext : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ) → AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ),
      Function.Injective ext ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)),
        f ∈ v.toValuationSubring ↔ ι f ∈ (ext v).toValuationSubring) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ)),
        (∀ f : ↥(ModularCurve.qExpFunctionFieldC κ Γ), f ∈ v.toValuationSubring ↔ ι f ∈ w.toValuationSubring) → ext v = w) ∧
      (∀ w : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K Γ), w.toValuationSubring.comap ι ≠ ⊤ →
        ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)), (ext v).ord (ι f) = v.ord f) ∧
      (∀ (v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (f : ↥(ModularCurve.qExpFunctionFieldC κ Γ)) (a : κ),
        v.HasValue f a ↔ (ext v).HasValue (ι f) (algebraMap κ K a)) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        v ∈ ModularCurve.ssPlacesQExp κ Γ p ↔ ext v ∈ ModularCurve.ssPlacesQExp K Γ p) ∧
      (∀ w ∈ ModularCurve.ssPlacesQExp K Γ p, ∃ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ), ext v = w) ∧
      (∀ v : AlgebraicCurve.Place κ ↥(ModularCurve.qExpFunctionFieldC κ Γ),
        ext (ModularCurve.qExpFrobeniusPlaceModL κ Γ p v) = ModularCurve.qExpFrobeniusPlaceModL K Γ p (ext v)) := by sorry
