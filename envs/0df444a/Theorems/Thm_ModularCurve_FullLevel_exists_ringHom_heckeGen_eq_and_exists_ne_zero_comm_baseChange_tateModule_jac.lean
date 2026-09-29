-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
-- name    : ModularCurve.FullLevel.exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:35.562543+00:00
-- url     : https://prove2.me/theorems/b93679e1-61c2-51db-af5b-ac8bfe3c47e3
-- title:
--   Cuspidal type of a newform in the full-level Tate module
-- statement:
--   Fix primes $q$ and $\lambda$ and an integer $M'\ge 1$ with $q\nmid M'$, and a local commutative $\mathbb{Z}_\lambda$-algebra $O'$ in which the image of $\lambda$ lies in the maximal ideal. Write $\mathrm{Jac}(q,M')$ for the product, indexed by `Idx q`, of copies of the Jacobian $J_H(q^2M')$ attached to $H=\ker\big((\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times\big)$, and $T_\lambda$ for the $\lambda$-adic Tate module, the group of sequences $(x_n)$ with $\lambda^n x_n=0$ and $\lambda x_{n+1}=x_n$. Let $T$ be a ring homomorphism from $\mathrm{HeckeAlg}=\mathbb{Z}[X_\ell:\ell\text{ prime}]$ and $G$ a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Z}/q)$ to $\mathrm{End}_{O'}\big(O'\otimes_{\mathbb{Z}_\lambda}T_\lambda\mathrm{Jac}(q,M')\big)$ acting on pure tensors through `tateHecke` and `tateGL2` respectively, and assume $T$ and $G$ commute elementwise. Assume the predicates `LevelAutInputs`, `HeckeGenCommute`, `GL2Laws` for $(q,M')$ and `HeckeDiamondInputsHAll` for level $q^2M'$ and $H$, and fix an $O'$-algebra structure on $\mathbb{C}$. Let $g$ be a weight-two newform on $\Gamma_0(q^2M')$ (a normalised eigenform whose eigensystem occurs at no proper divisor of the level), $S$ a finite set of naturals, and $\chi_g$ a ring homomorphism from the weight-two level-$q^2M'$ Hecke algebra away from $S$ to $\mathbb{C}$ sending each $T_\ell$, $\ell$ prime with $\ell\nmid q^2M'$ and $\ell\notin S$, to the $\ell$-th $q$-expansion coefficient of $g$. Let $\Phi$ be an adelic lift of $g$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, $V$ a $\mathbb{C}$-representation of $\mathrm{GL}_2(\mathbb{Q}_q)$ whose subspace of vectors fixed by `gl2CongruenceSubgroup q 1` is finite-dimensional, and $f:V\to\mathrm{AdelicSpan}\,\Phi$ an injective equivariant linear map whose range is the $\mathbb{C}$-span of the $\mathrm{GL}_2(\mathbb{Q}_q)$-orbit of the distinguished element of $\mathrm{AdelicSpan}\,\Phi$. Finally let $\theta:\mathbb{F}_{q^2}^\times\to\mathbb{C}^\times$ and let $W$ be a subrepresentation of the $\mathrm{GL}_2(\mathbb{Z}/q)$-representation on those fixed vectors which is cuspidal of type $\theta$, i.e. of dimension $q-1$, with no nonzero vector fixed by all upper unipotents, with scalars acting as the identity, and with the charpoly identity relating the torus elements to the induced representation. Then there exist a ring homomorphism $h:\mathrm{HeckeAlg}\to\mathbb{C}$ with $h(X_\ell)=\chi_g(T_\ell)$ for all primes $\ell\nmid q^2M'$ outside $S$, and a nonzero $\mathbb{C}$-linear map $\varphi$ from $W$ to $\mathbb{C}\otimes_{O'}\big(O'\otimes_{\mathbb{Z}_\lambda}T_\lambda\mathrm{Jac}(q,M')\big)$ which intertwines the action of each $x\in\mathrm{GL}_2(\mathbb{Z}/q)$ on $W$ with the base change of $G(x)$, and satisfies $(T t)_\mathbb{C}\circ\varphi=h(t)\,\varphi$ for every $t\in\mathrm{HeckeAlg}$.
--
--   This is the Eichler–Shimura comparison at full level $q$: the cuspidal type $\theta$ carried by the local automorphic representation of a newform of level $q^2M'$ occurs, with the Hecke eigencharacter of that newform, in the Tate module of the full-level Jacobian. It is consumed by the two `FullLevelTate` existence statements producing the full-level Tate-module datum with non-trivial $W$-isotypic eigenspace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ReductionFunctor
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.FullLevel.exists_ringHom_heckeGen_eq_and_exists_ne_zero_comm_baseChange_tateModule_jac
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (lam : ℕ) [Fact lam.Prime]
    (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[lam] O']
    (hlamO' : (lam : O') ∈ IsLocalRing.maximalIdeal O')
    (T : ModularCurve.HeckeAlg →+*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hT : ∀ (t : ModularCurve.HeckeAlg) (a : O') (x : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      T t (a ⊗ₜ[ℤ_[lam]] x) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateHecke q M' lam t x)
    (G : CuspidalType.GL2 q →*
      Module.End O' (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')))
    (hG : ∀ (x : CuspidalType.GL2 q) (a : O') (y : TateModule lam (ModularCurve.FullLevel.Jac q M')),
      G x (a ⊗ₜ[ℤ_[lam]] y) = a ⊗ₜ[ℤ_[lam]] ModularCurve.FullLevel.tateGL2 q M' lam x y)
    (hTG : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q), T t * G x = G x * T t)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hHC : ModularCurve.FullLevel.HeckeGenCommute q M')
    (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (hin : ModularCurve.HeckeDiamondInputsHAll (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    [Algebra O' ℂ]
    (g : CuspForm (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) 2) (hg : g.IsNewform)
    (S : Finset ℕ) (chig : CuspForm.heckeAlgebra (q ^ 2 * M') 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦg : g.IsAdelicLiftOf Φ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    [FiniteDimensional ℂ
      ↥(LocalNewvector.fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)]
    (f : V →ₗ[ℂ] LocalNewvector.AdelicSpan Φ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) (hfinj : Function.Injective f)
    (hfrange : LinearMap.range f =
      Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (θ : (GaloisField q 2)ˣ →* ℂˣ)
    (W : Subrepresentation (LocalNewvector.gl2ReductionRep q V))
    (hθ : CuspidalType.IsCuspidalOfType θ W.toRepresentation) :
    ∃ hk : ModularCurve.HeckeAlg →+* ℂ,
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ q ^ 2 * M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
          hk (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) ∧
      ∃ φ : ↥W.toSubmodule →ₗ[ℂ] ℂ ⊗[O'] (O' ⊗[ℤ_[lam]] TateModule lam (ModularCurve.FullLevel.Jac q M')),
        φ ≠ 0 ∧
        (∀ x : CuspidalType.GL2 q, φ ∘ₗ W.toRepresentation x = (G x).baseChange ℂ ∘ₗ φ) ∧
        (∀ t : ModularCurve.HeckeAlg, (T t).baseChange ℂ ∘ₗ φ = hk t • φ) := by sorry
