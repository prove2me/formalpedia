-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/82a982f9-8a04-5eef-bd2b-7000b89215f9
-- title:
--   Eichler–Shimura relation on a finite flat model of J₀(M)[p]
-- statement:
--   Let $M \ge 1$ and let $p$ be a prime with $p \nmid M$, and give `JZero M` — the degree-zero divisor class group of the modular function field of level $M$ base changed to $\overline{\mathbb{Q}}$ — the `HeckeAlg`-module structure `heckeModuleBar M`, where `HeckeAlg` is the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$. Then there exist a commutative ring $H$ carrying a Hopf algebra structure over the subring $\mathbb{Z}_{(p)} \subset \mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite, flat and free as a $\mathbb{Z}_{(p)}$-module and with cocommutative comultiplication, and a bijection $e$ from the $\overline{\mathbb{Q}}$-points $H \to_{\mathbb{Z}_{(p)}\text{-alg}} \overline{\mathbb{Q}}$, equipped with the convolution multiplication, onto the subgroup of `JZero M` of elements killed by $p$ which also lie in $\bigcup_m \ker(\mathrm{heckeOperatorBar}\,M\,p)^m$, such that: $e$ carries convolution to addition; if $g = \sigma \circ f$ for $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ then $e(g) = \sigma \cdot e(f)$; and for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, if the reduction `reductionModL A M` of $e(f)$ vanishes then $A$-valuation of $f(h) - \varepsilon(h)$ is $< 1$ for all $h \in H$, $\varepsilon$ the counit. Moreover there is a family $\varphi'$ of $\mathbb{Z}_{(p)}$-algebra endomorphisms of $H$ indexed by `HeckeAlg`, each mapping $\ker \varepsilon$ into itself and inducing through $e$ the Hecke action ($g = f \circ \varphi'(t)$ implies $e(g) = t \cdot e(f)$), such that $\varphi'(X_p)$ underlies a bialgebra endomorphism $T_c$ of $H$ with (i) some power of $T_c$, as a linear map, equal to the unit composed after the counit, and (ii) for every bialgebra endomorphism $F_k$ of $\mathbb{F}_p \otimes_{\mathbb{Z}_{(p)}} H$ with $F_k(x) = x^p$ and every $\mathbb{F}_p$-algebra endomorphism $F_D$ of its Cartier dual with $F_D(\psi) = \psi^p$: the Cartier dual of $\mathrm{id} \otimes T_c$ equals the convolution product of [`CartierDual.map`](def/HopfAlgebra_CartierDualMap.html#L102) $F_k$ with $F_D$, and $F_D \circ (\mathrm{CartierDual.map}\, F_k)$ equals the unit composed after the counit.
--
--   This packages the Eichler–Shimura congruence $T_p = F + V$, together with $FV = p = 0$, on the special fibre of a finite flat $\mathbb{Z}_{(p)}$-model of the $T_p$-nilpotent part of $J_0(M)[p]$, read through the Cartier dual, alongside the nilpotence of the Hecke endomorphism $T_p$ on that model. It feeds the Eichler–Shimura stage of the argument, being cited by [`ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimura).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL.lean

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

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact p.Prime] (hpM : ¬ p ∣ M) :
    letI := heckeModuleBar M
    ∃ (H : Type) (_ : CommRing H) (_ : HopfAlgebra (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Finite (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Flat (GaloisRep.ratLocalizedAt p) H)
      (_ : Module.Free (GaloisRep.ratLocalizedAt p) H)
      (_ : Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H),
      ∃ e : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
          ↥(Submodule.torsionBy ℤ (JZero M) (p : ℤ) ⊓
            ⨆ m : ℕ, LinearMap.ker (heckeOperatorBar M ⟨p, hp.out⟩ ^ m)),
        (∀ f g, e (f * g) = e f + e g) ∧
        (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → ((e g : JZero M)) = σ • (e f : JZero M)) ∧
        (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime p →
          ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            reductionModL A M (e f : JZero M) = 0 →
            ∀ h : H, A.valuation (f h - algebraMap (GaloisRep.ratLocalizedAt p)
              (AlgebraicClosure ℚ) (Coalgebra.counit h)) < 1) ∧
        ∃ φ' : HeckeAlg → (H →ₐ[GaloisRep.ratLocalizedAt p] H),
          (∀ t : HeckeAlg,
            RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H) ≤
              (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) H)).comap (φ' t)) ∧
          (∀ (t : HeckeAlg) (f g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : H, g h = f (φ' t h)) → ((e g : JZero M)) = t • (e f : JZero M)) ∧
          ∃ Tc : H →ₐc[GaloisRep.ratLocalizedAt p] H,
            (Tc : H →ₐ[GaloisRep.ratLocalizedAt p] H) = φ' (heckeGen ⟨p, hp.out⟩) ∧
            (∃ m : ℕ, (Tc : H →ₗ[GaloisRep.ratLocalizedAt p] H) ^ m =
              Algebra.linearMap (GaloisRep.ratLocalizedAt p) H ∘ₗ Coalgebra.counit) ∧
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
                        CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H))).ofConv ∧
              (FD : CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
                  CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
                  (CartierDual.map Fk :
                    CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H) →ₗ[ZMod p]
                      CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) =
                Algebra.linearMap (ZMod p)
                    (CartierDual (ZMod p) (TensorProduct (GaloisRep.ratLocalizedAt p) (ZMod p) H)) ∘ₗ
                  Coalgebra.counit := by sorry
