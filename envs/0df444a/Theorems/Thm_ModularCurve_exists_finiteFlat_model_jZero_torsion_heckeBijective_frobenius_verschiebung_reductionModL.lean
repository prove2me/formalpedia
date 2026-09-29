-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/9a9088a4-4cad-50b8-a57a-70a8e0d7f1cd
-- title:
--   Finite flat model of the Tₚ-bijective part of J₀(M)[p^k]
-- statement:
--   Let $M\ge 1$, let $p$ be a prime not dividing $M$, and let $k\in\mathbb N$. Write $R=\mathbb Z_{(p)}$ for the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, and $J_0(M)=$ `JZero M`, the group of degree-zero divisor classes of the modular function field of level $M$ base changed to $\overline{\mathbb Q}$. The assertion is that there exist a commutative ring $H$ carrying a Hopf algebra structure over $R$ which is finite, flat and free as an $R$-module and has cocommutative comultiplication, together with a bijection $e$ from the set of $R$-algebra homomorphisms $H\to\overline{\mathbb Q}$, regarded as a monoid under convolution, onto the subgroup $\bigcap_{m}T_p^{m}\bigl(J_0(M)[p^k]\bigr)$, where $T_p$ is `heckeOperatorBar M ⟨p, _⟩` and $J_0(M)[p^k]$ is the $\mathbb Z$-torsion submodule annihilated by $p^k$, such that: (i) $e(f\star g)=e(f)+e(g)$; (ii) for $\sigma\in\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and points $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, one has $e(g)=\sigma\cdot e(f)$; (iii) for every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ and every $f$, if `reductionModL A M (e f) = 0` then $A$-valuation of $f(h)-\varepsilon(h)$ is $<1$ for all $h\in H$, $\varepsilon$ the counit; (iv) the $p^k$-th convolution power of the identity map of $H$ is the unit of the convolution monoid; and (v) there is a bijective $R$-bialgebra endomorphism $T_c$ of $H$ inducing $T_p$ through $e$ (if $g(h)=f(T_c h)$ for all $h$ then $e(g)=T_p(e(f))$), with the property that for every $\mathbb F_p$-bialgebra endomorphism $F_k$ of $\mathbb F_p\otimes_R H$ with $F_k(x)=x^p$ and every $\mathbb F_p$-algebra endomorphism $F_D$ of the Cartier dual of $\mathbb F_p\otimes_R H$ with $F_D(\psi)=\psi^p$, the Cartier dual map of $\mathrm{id}\otimes T_c$ equals the convolution product of the Cartier dual map of $F_k$ with $F_D$, as $\mathbb F_p$-linear endomorphisms of that Cartier dual.
--
--   This packages the Eichler–Shimura relation $T_p = \mathrm{Frob}_p + \mathrm{Ver}_p$ at a prime $p$ of good reduction into a finite flat $\mathbb Z_{(p)}$-Hopf-algebra model of the $T_p$-bijective part of the $p^k$-torsion of $J_0(M)$, with the Galois action, the reduction map at places above $p$, the $p^k$-torsion condition and the action of $T_p$ all expressed on the points of that model and its Cartier dual in characteristic $p$. It is used by the two statements describing the action of inertia at $p$ on such torsion points as multiplication by an integer.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeBijective_frobenius_verschiebung_reductionModL
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℕ) :
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Flat (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) H)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H),
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(⨅ m : ℕ, Submodule.map (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)
            (Submodule.torsionBy ℤ (JZero M) ((p : ℤ) ^ k))),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero M)) = σ • (e f : JZero M)) ∧
        (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
          ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            reductionModL A M (e f : JZero M) = 0 →
            ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt p)
              (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) ∧
        WithConv.toConv (LinearMap.id : H →ₗ[GaloisRep.ratLocalizedAt p] H) ^ (p ^ k) = 1 ∧
        ∃ Tc : H →ₐc[GaloisRep.ratLocalizedAt p] H,
          Function.Bijective Tc ∧
          (∀ f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = f (Tc h)) →
              ((e g : JZero M)) = heckeOperatorBar M ⟨p, hp.out⟩ (e f : JZero M)) ∧
          ∀ (Fk : TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H →ₐc[ZMod p]
              TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H),
            (∀ x, Fk x = x ^ p) →
          ∀ (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₐ[ZMod p]
              CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)),
            (∀ ψ, FD ψ = ψ ^ p) →
            (CartierDual.map (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) Tc) :
                CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
                  CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) =
              (WithConv.toConv
                  (CartierDual.map Fk :
                    CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
                      CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) *
                WithConv.toConv
                  (FD :
                    CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
                      CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H))).ofConv := by sorry
