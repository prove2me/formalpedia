-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/b27d9d88-48ac-54b8-9f21-0a8f56fab0bb
-- title:
--   Basis of the n-torsion after a finite étale cover
-- statement:
--   Let $S$ be a commutative ring, let $f : A \to \operatorname{Spec} S$ be a scheme over $\operatorname{Spec} S$, and let $L$ be a `RelativeGroupLaw` for $f$: a group structure on each set $\mathrm{SchemeHomOver}\,t\,f = \{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over a base morphism $t : T \to \operatorname{Spec} S$, natural in $T$ under precomposition; assume $L$ is commutative, and fix $n, m \in \mathbb{N}$. Assume given a finite étale $S$-algebra $B$ and a closed immersion $\iota : \operatorname{Spec} B \to A$ with $\iota$ followed by $f$ equal to the structure morphism $\operatorname{Spec}$ of $S \to B$, which represents the $n$-torsion in the sense that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and every $y \in \mathrm{SchemeHomOver}\,t\,f$, the $n$-fold power $L.\mathrm{nsmul}\,t\,n\,y$ is the neutral section if and only if $y$ factors through $\iota$. Assume further that for every algebraically closed field $k$ and every ring homomorphism $s_k : S \to k$ there are sections $P_1, \dots, P_m$ of $f$ over $\operatorname{Spec} k$, each killed by $n$, whose combinations $L.\mathrm{finComb}\,P\,c = \prod_i P_i^{c_i}$ for $c \in (\mathbb{Z}/n)^m$ (coefficients taken from `Fin n`) are pairwise distinct and exhaust the sections killed by $n$. The conclusion asserts the existence of a commutative ring $S'$ which is a finite étale and faithfully flat $S$-algebra, together with sections $P_1, \dots, P_m$ of $f$ over $\operatorname{Spec} S'$ with each $L.\mathrm{nsmul}\,n\,P_i$ neutral, such that for every algebraically closed field $k$ and every ring homomorphism $s_k : S' \to k$: the morphisms underlying the combinations $L.\mathrm{finComb}\,P\,c$, restricted along $\operatorname{Spec} s_k$, are pairwise distinct for distinct $c \in (\mathbb{Z}/n)^m$; and every section $Q$ of $f$ over $\operatorname{Spec} k$ via $s_k \circ (S \to S')$ killed by $n$ has underlying morphism equal to the restriction along $\operatorname{Spec} s_k$ of $L.\mathrm{finComb}\,P\,c$ for some $c$.
--
--   This is the descent step for the "torsor of bases": the hypotheses say that the $n$-torsion of $f$ is a finite étale closed subscheme and that bases of length $m$ exist on each geometric fibre, and the conclusion produces a single $m$-tuple of $n$-torsion sections over a finite étale faithfully flat base change which is a basis at every geometric point of the new base. It is used in the construction of the étale trivialisation of the $n$-torsion of an abelian scheme, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_etale_typeGroup_nsmul_eq_one_iff_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n m : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom sk)) n (P i) = L.one (Spec.map (CommRingCat.ofHom sk))) ∧
        (∀ c c' : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c' i : ℕ)) → c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin m → Fin n, L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) = Q)) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S') (_ : Module.Finite S S') (_ : Algebra.Etale S S')
      (_ : Module.FaithfullyFlat S S')
      (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f),
      (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
        L.one (Spec.map (CommRingCat.ofHom (algebraMap S S')))) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (c c' : Fin m → Fin n),
        Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 =
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c' i : ℕ))).1 → c = c') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
        L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
          L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
        ∃ c : Fin m → Fin n,
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1) := by sorry
