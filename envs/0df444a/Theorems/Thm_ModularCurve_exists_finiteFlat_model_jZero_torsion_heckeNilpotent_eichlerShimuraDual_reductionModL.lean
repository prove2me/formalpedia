-- Prove2me | Theorems.Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL
-- name    : ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/221c0b11-d2fb-5480-a975-e43c018e59b9
-- title:
--   Eichler–Shimura relation on a finite flat model of J₀(M)[p]
-- statement:
--   Let $M\ge 1$ and let $p$ be a prime with $p \nmid M$, and give $\mathrm{JZero}\,M$ — the degree-zero divisor class group $\mathrm{Pic}^0$ of the modular function field of level $M$ base-changed to $\overline{\mathbb{Q}}$, i.e. $J_0(M)(\overline{\mathbb{Q}})$ — its module structure over $\mathrm{HeckeAlg}=\mathbb{Z}[X_\ell : \ell \text{ prime}]$ in which the variable $X_\ell$ acts by `heckeOperatorBar`. The assertion is the existence of a commutative ring $H$ carrying a Hopf algebra structure over the subring $\mathbb{Z}_{(p)}\subset\mathbb{Q}$ of rationals whose denominator is coprime to $p$, finite, flat and free as a $\mathbb{Z}_{(p)}$-module and cocommutative as a coalgebra, together with a bijection $e$ from the set of $\mathbb{Z}_{(p)}$-algebra homomorphisms $H\to\overline{\mathbb{Q}}$, equipped with the convolution multiplication, onto the subgroup of $J_0(M)(\overline{\mathbb{Q}})$ consisting of the points killed by $p$ that are also killed by some power of the operator attached to $p$, such that: (i) $e(f\ast g)=e(f)+e(g)$; (ii) for every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and all $f,g$ with $g(h)=\sigma(f(h))$ for all $h\in H$, one has $e(g)=\sigma\cdot e(f)$; (iii) for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, and every $f$ whose image $e(f)$ has zero reduction under `reductionModL` at $A$, one has $A$-valuation $<1$ of $f(h)-\varepsilon(h)$ for all $h\in H$, where $\varepsilon$ is the counit (so $f$ reduces to the identity section); and (iv) there is a family $\varphi'$ of $\mathbb{Z}_{(p)}$-algebra endomorphisms of $H$ indexed by $\mathrm{HeckeAlg}$, each mapping the augmentation ideal $\ker\varepsilon$ into itself, inducing the Hecke action through $e$ (if $g(h)=f(\varphi'(t)(h))$ for all $h$ then $e(g)=t\cdot e(f)$), and such that $\varphi'(X_p)$ underlies a bialgebra endomorphism $T$ of $H$ with the following property: for every $\mathbb{F}_p$-bialgebra endomorphism $F_k$ of $\mathbb{F}_p\otimes_{\mathbb{Z}_{(p)}}H$ with $F_k(x)=x^p$ and every $\mathbb{F}_p$-algebra endomorphism $F_D$ of the Cartier dual of $\mathbb{F}_p\otimes H$ with $F_D(\psi)=\psi^p$, the Cartier dual of the base change of $T$ equals, as an $\mathbb{F}_p$-linear endomorphism of that dual, the convolution product of the Cartier dual of $F_k$ with $F_D$.
--
--   This packages the $T_p$-nilpotent part of $J_0(M)[p]$ as the $\overline{\mathbb{Q}}$-points of a finite flat group scheme over $\mathbb{Z}_{(p)}$, Galois- and Hecke-equivariantly and compatibly with reduction at places above $p$, and records the Eichler–Shimura congruence $T_p = F + V$ on the special fibre in the form of a convolution identity on the Cartier dual. It is used to derive the strengthened statement [`ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL`](thm.html#ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_frobenius_verschiebung_reductionModL), which adds the relations between Frobenius and Verschiebung on the special fibre needed for the local analysis at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL.lean

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

theorem ModularCurve.exists_finiteFlat_model_jZero_torsion_heckeNilpotent_eichlerShimuraDual_reductionModL
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
