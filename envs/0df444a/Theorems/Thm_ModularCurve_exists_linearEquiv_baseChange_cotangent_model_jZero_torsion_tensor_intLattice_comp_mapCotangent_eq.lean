-- Prove2me | Theorems.Thm_ModularCurve_exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq
-- name    : ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/a0212c14-1255-54ab-bb19-4ecfba469047
-- title:
--   Cotangent space of a p-torsion model of J₀(N) versus S₂(Γ₀(N),ℤ)⊗ k
-- statement:
--   Fix $N\ge 1$ and a prime $p$ with $p\ne 2$ and $p\nmid N$, and write $\mathbf Z_{(p)}$ for [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $p$. Let $A$ be a commutative ring carrying a cocommutative Hopf algebra structure over $\mathbf Z_{(p)}$ which is finite and flat as a $\mathbf Z_{(p)}$-module, with counit $\varepsilon$ and augmentation ideal $I=\ker\varepsilon$, and let $k$ be an algebraically closed field of characteristic $p$ that is a $\mathbf Z_{(p)}$-algebra. The Hecke algebra is $\mathbf T=\mathbf Z[\,\ell\ \text{prime}\,]$, the polynomial ring `MvPolynomial Nat.Primes ℤ`; it acts on $J_0(N)=\mathrm{Pic}^0$ of the base-changed modular function field over $\overline{\mathbf Q}$ through `heckeModuleBar N` (the divisorial Hecke action when the operators commute, and the zero specialisation otherwise), and on the lattice [`CuspForm.intLattice N 2`](def/CuspForm_IntegralStructure.html#L3) spanned by weight-two cusp forms on $\Gamma_0(N)$ all of whose $q$-coefficients are rational integers through [`CuspForm.latticeHeckeFamily N`](def/CuspForm_LatticeHeckeFamily.html#L13), whose generator at $\ell$ acts as $U_\ell$ if $\ell\mid N$ and as $T_\ell$ otherwise. Assume given a bijection $e$ from the set of $\mathbf Z_{(p)}$-algebra maps $A\to\overline{\mathbf Q}$, regarded as a group under convolution, onto the $p$-torsion submodule $\{x\in J_0(N):p\,x=0\}$ such that $e(fg)=e(f)+e(g)$; such that for every $\sigma\in\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$ and every pair $f,g$ with $g=\sigma\circ f$ pointwise on $A$ one has $e(g)=\sigma\cdot e(f)$; and a family $\varphi\colon\mathbf T\to\mathrm{End}_{\mathbf Z_{(p)}\text{-alg}}(A)$ such that for every $t$ and every pair $f,g$ with $g=f\circ\varphi(t)$ pointwise one has $e(g)=t\cdot e(f)$, together with the hypothesis that each $\varphi(t)$ carries $I$ into $I$. The conclusion is that there exists a $k$-linear isomorphism $\Xi\colon k\otimes_{\mathbf Z_{(p)}} I/I^2\;\xrightarrow{\ \sim\ }\;k\otimes_{\mathbf Z}\mathrm{intLattice}(N,2)$ which, for every $t\in\mathbf T$, intertwines the base change to $k$ of the map on $I/I^2$ induced by $\varphi(t)$ with the base change to $k$ of the action of $t$ on the lattice.
--
--   This is the identification of the cotangent space at the origin of a finite flat $\mathbf Z_{(p)}$-group-scheme model of $J_0(N)[p]$ with the mod $p$ reduction of the integral lattice of weight-two cusp forms on $\Gamma_0(N)$, compatibly with the Hecke action; the hypotheses on $e$ and $\varphi$ say precisely that $\mathrm{Spec}\,A$ is such a model with its Galois and Hecke structure. It is used in the count of the kernels of the Hecke operators on this cotangent space, [`ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient`](thm.html#ModularCurve.natCard_iInf_ker_mapCotangent_baseChange_model_jZero_torsion_eq_card_torsionBySet_intLattice_quotient), which feeds the multiplicity-one input to the level-lowering and lifting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_LatticeHeckeFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve
open scoped TensorProduct

theorem ModularCurve.exists_linearEquiv_baseChange_cotangent_model_jZero_torsion_tensor_intLattice_comp_mapCotangent_eq
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N)
    (A : Type) [CommRing A] [HopfAlgebra (GaloisRep.ratLocalizedAt p) A]
    [Module.Finite (GaloisRep.ratLocalizedAt p) A] [Module.Flat (GaloisRep.ratLocalizedAt p) A]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) A]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra (GaloisRep.ratLocalizedAt p) k] :
    letI := heckeModuleBar N
    letI := (CuspForm.latticeHeckeFamily N).module
    ∀ e : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃
        ↥(Submodule.torsionBy ℤ (JZero N) ((p : ℤ) ^ 1)),
      (∀ f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) →
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
          (∀ h : A, g h = σ (f h)) → ((e g : JZero N)) = σ • (e f : JZero N)) →
      ∀ φ : HeckeAlg → (A →ₐ[GaloisRep.ratLocalizedAt p] A),
        (∀ (t : HeckeAlg) (f g : WithConv (A →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
            (∀ h : A, g h = f (φ t h)) → ((e g : JZero N)) = t • (e f : JZero N)) →
      ∀ hφI : ∀ t : HeckeAlg,
          RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A) ≤
            (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A)).comap (φ t),
      ∃ Ξ : k ⊗[GaloisRep.ratLocalizedAt p]
            (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A)).Cotangent ≃ₗ[k]
          k ⊗[ℤ] ↥(CuspForm.intLattice N 2),
        ∀ t : HeckeAlg,
          (Ξ : k ⊗[GaloisRep.ratLocalizedAt p]
                (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A)).Cotangent →ₗ[k]
              k ⊗[ℤ] ↥(CuspForm.intLattice N 2)) ∘ₗ
            ((RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A)).mapCotangent
                (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A))
                (φ t) (hφI t)).baseChange k =
          (DistribSMul.toLinearMap ℤ ↥(CuspForm.intLattice N 2) t).baseChange k ∘ₗ
            (Ξ : k ⊗[GaloisRep.ratLocalizedAt p]
                (RingHom.ker (Bialgebra.counitAlgHom (GaloisRep.ratLocalizedAt p) A)).Cotangent →ₗ[k]
              k ⊗[ℤ] ↥(CuspForm.intLattice N 2)) := by sorry
