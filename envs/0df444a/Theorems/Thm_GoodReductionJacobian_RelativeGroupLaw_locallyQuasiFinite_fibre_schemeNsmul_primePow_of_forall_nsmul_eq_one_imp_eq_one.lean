-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/45938f7d-1868-5408-8055-71fd55846d38
-- title:
--   Multiplication by p^k on the (p)-fibre is locally quasi-finite
-- statement:
--   Let $p$ be a prime and let $g \colon G \to \operatorname{Spec}\mathbf{Z}$ be a morphism of schemes that is locally of finite type, equipped with a relative group law $L$ over $\mathbf{Z}$: for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec}\mathbf{Z}$, a multiplication, a unit and an inversion on the set of pairs $(\varphi \colon T \to G)$ with $\varphi$ followed by $g$ equal to $t$, satisfying associativity, the two unit laws and left inversion, with multiplication compatible with base change along any $\psi \colon T' \to T$ over $\operatorname{Spec}\mathbf{Z}$. Assume in addition that this multiplication is commutative for all $T$ and $t$, and that for every algebraically closed field $K$ of characteristic $p$, every $k \in \mathbf{N}$ and every point $x$ of $G$ over $\operatorname{Spec} K \to \operatorname{Spec}\mathbf{Z}$, the relation $p^k \cdot x = e$ (where $n \cdot x$ denotes the $n$-fold iterate of multiplication by $x$ starting from the unit) forces $x = e$. Then for every point $s$ of $\operatorname{Spec}\mathbf{Z}$ whose prime ideal is $(p)$ and every $k > 0$, the morphism $\operatorname{schemeNsmul}(p^k)$ attached to the fibre group law $L_s$ over the residue field $\kappa(s)$ — that is, multiplication by $p^k$ on the fibre $G_s = G \times_{\operatorname{Spec}\mathbf{Z}} \operatorname{Spec}\kappa(s)$, obtained by applying $p^k \cdot$ to the identity point of $G_s$ — is locally quasi-finite.
--
--   This is the assertion that on a commutative group scheme over $\mathbf{Z}$ which is locally of finite type, triviality of $p$-power torsion on geometric points of characteristic $p$ makes multiplication by $p^k$ locally quasi-finite on the fibre at $(p)$. It supplies one of the hypotheses in the construction of the good identity component of the Néron model used in [`ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin`](thm.html#ModularCurve.nonempty_jZeroNeronIdentityComponentGood_of_dRModelPackage_of_ffPin); note that the hypothesis concerns points only, the torsion subscheme itself being typically infinitesimal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one
    (p : ℕ) [Fact p.Prime] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of ℤ)} [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    (htors : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) g),
      L.nsmul _ (p ^ k) x = L.one _ → x = L.one _) :
    ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite ((L.fibre s).schemeNsmul (p ^ k)) := by sorry
