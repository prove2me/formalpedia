-- Prove2me | Theorems.Thm_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
-- name    : ModularCurve.exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/4e592669-57ed-570b-a854-4c72db041d35
-- title:
--   Ordinary idempotent on a p-divisible subgroup of J_H
-- statement:
--   Fix a prime $p$, an integer $M \ne 0$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ and a set $S$ of naturals, and write $J_H = \mathrm{Pic}^0$ of the base change to $\overline{\mathbb{Q}}$ of the function field of $X_H$, with $T_p J_H$ the group of sequences $(x_n)$ in $J_H$ satisfying $p^n x_n = 0$ and $p\,x_{n+1} = x_n$. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on $T_p J_H$ compatibly with the $\mathbb{Z}_p$-action, the action being faithful (`hfaith`), and let $\mathrm{op}$ assign to each generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a $T_\ell$ for $\ell$ prime, $\ell \notin S$, $\ell \nmid M$; a $U_q$ for $q$ prime dividing $M$; a diamond $\langle d \rangle$ for $d \in (\mathbb{Z}/M)^\times$) an element of $\mathbb{T}$ acting on $T_p J_H$ as the endomorphism `tateGenOpH` induced by the corresponding Hecke or diamond endomorphism `genOpH` of $J_H$, and assume these elements generate $\mathbb{T}$ as a $\mathbb{Z}_p$-algebra. Let $S'$ be an idempotent splitting of $\mathbb{T}$, that is, a complete orthogonal family of idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals and satisfying $e_i \in \mathfrak{m}_j \iff i \ne j$, and let $i_0$ be an index with $\mathrm{op}(U_p) \notin \mathfrak{m}_{i_0}$. Let $O$ be a commutative domain with an injective structure map to $\overline{\mathbb{Q}}$, and $\mathcal{G}$ a $p$-divisible group over $O$ of height $h$ (finite free cocommutative Hopf algebras $\mathcal{G}.\mathrm{level}\,v$ of rank $p^{vh}$ with surjective transition bialgebra maps whose kernels are the $p^v$-torsion ideals). Assume given an injective additive map $\Delta$ from the direct limit $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$ of the point groups into $J_H$, and a $\mathbb{Z}_p$-linear map $e$ on Tate modules computing componentwise as $\Delta$. Assume further a transition-compatible family $u = (u_v)$ of bialgebra endomorphisms of the levels which realises $U_p$ on points, in the sense that for every level $v$ and point $x$, $\Delta$ of the point obtained by precomposing the algebra map of $x$ with $u_v$ equals `genOpH` of $U_p$ applied to $\Delta(x)$; and assume every generator $g$ is realised on points in this sense by some transition-compatible family. The conclusion asserts the existence of transition-compatible families $\varepsilon = (\varepsilon_v)$ and $w = (w_v)$ of bialgebra endomorphisms of the levels such that each $\varepsilon_v$ is idempotent, $\varepsilon_v$ commutes with $u_v$, $\varepsilon_v \circ w_v = w_v = w_v \circ \varepsilon_v$, and $w_v \circ (u_v \circ \varepsilon_v) = \varepsilon_v = (u_v \circ \varepsilon_v) \circ w_v$; moreover $\varepsilon_v$ commutes with every transition-compatible family realising any generator on points, any two such realising families commute levelwise, and there is a $\mathbb{Z}_p$-endomorphism $E$ of the Tate module of $\mathcal{G}(\overline{\mathbb{Q}})$ acting componentwise by precomposition with $\varepsilon_v$ (whenever the $n$-th component of $x$ is the class of a point $f$ at level $v$, the $n$-th component of $Ex$ is the class of $f$ precomposed with $\varepsilon_v$), satisfying $e(Ey) = e_{i_0} \cdot e(y)$ for all $y$.
--
--   This is the supplier of Hida's ordinary projector in the present setting: the corner idempotent $e_{i_0}$ of the Hecke algebra cut out by invertibility of $U_p$ is realised, on a $p$-divisible group mapping into $J_H$, by a transition-compatible family of bialgebra idempotents on the finite levels, with $U_p$ made invertible on the resulting direct factor (the families $w$ being the inverse). It feeds the ordinary-corner Frobenius law for the Galois representation on $T_p J_H$, used in [`ModularCurve.exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary`](thm.html#ModularCurve.exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (S : Set ℕ)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)

    {O : Type} [CommRing O] [IsDomain O] [Algebra O (AlgebraicClosure ℚ)]
    (hinj : Function.Injective (algebraMap O (AlgebraicClosure ℚ)))
    {h : ℕ} (𝒢 : PDivisibleGroup O p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H) (hΔ : Function.Injective Δ)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (he : ∀ (y : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e y : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n = Δ ((y : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))

    (u : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v)
    (hut : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huΔ : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
        ((PDivisibleGroup.Point.toAlgHom x).comp (u v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
        ModularCurve.genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (hgenG : ∀ g : CohCarrier.Gen M S, ∃ ψ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) :
    ∃ (ε w : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
      (∀ v : ℕ, (ε v).comp (ε v) = ε v) ∧
      (∀ v : ℕ, (𝒢.transition v).comp (ε (v + 1)) = (ε v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v)) ∧
      (∀ v : ℕ, (𝒢.transition v).comp (w (v + 1)) = (w v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, (ε v).comp (w v) = w v) ∧ (∀ v : ℕ, (w v).comp (ε v) = w v) ∧
      (∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v) ∧
      (∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v) ∧

      (∀ (g : CohCarrier.Gen M S) (ψ : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
        (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        ∀ v : ℕ, (ε v).comp (ψ v) = (ψ v).comp (ε v)) ∧

      (∀ (g g' : CohCarrier.Gen M S) (ψ ψ' : ∀ v : ℕ, 𝒢.level v →ₐc[O] 𝒢.level v),
        (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        (∀ v : ℕ, (𝒢.transition v).comp (ψ' (v + 1)) = (ψ' v).comp (𝒢.transition v)) →
        (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (ψ' v : 𝒢.level v →ₐ[O] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g' (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))) →
        ∀ v : ℕ, (ψ v).comp (ψ' v) = (ψ' v).comp (ψ v)) ∧

      ∃ Eop : Module.End ℤ_[p] (TateModule p (𝒢.Points (AlgebraicClosure ℚ))),
        (∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n v : ℕ) (f : 𝒢.Point (AlgebraicClosure ℚ) v),
          𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul f) = (x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n →
          ((Eop x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n =
            𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
              ((PDivisibleGroup.Point.toAlgHom f).comp (ε v : 𝒢.level v →ₐ[O] 𝒢.level v))))) ∧
        ∀ y : TateModule p (𝒢.Points (AlgebraicClosure ℚ)), e (Eop y) = (S'.e i₀) • e y := by sorry
