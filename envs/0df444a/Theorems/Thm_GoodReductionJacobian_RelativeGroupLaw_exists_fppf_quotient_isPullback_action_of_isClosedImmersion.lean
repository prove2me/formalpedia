-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fppf_quotient_isPullback_action_of_isClosedImmersion
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f82be015-c6ba-5abc-8baa-2cf5ebb48aef
-- title:
--   Existence of the fppf quotient G/N as a scheme
-- statement:
--   Let $k$ be an algebraically closed field and let $f : G \to \operatorname{Spec} k$ be separated and quasi-compact, equipped with a relative group law $L$ over $k$: functorial multiplication, unit and inverse operations on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, satisfying associativity, the two unit laws, left inversion, and compatibility with base change along morphisms $T' \to T$ over $k$. Assume $f$ is smooth of relative dimension $g$. Let $i : N \to G$ be a closed immersion, let $L_N$ be a relative group law on $i$ followed by $f$, with $i \circ f$ smooth of relative dimension $h$, and assume: (i) $i$ is multiplicative on points, i.e. $i \circ (x \cdot_{L_N} y) = (i \circ x) \cdot_L (i \circ y)$ for all $T$-points $x, y$ of $N$ over $k$; (ii) $N$ is normal on points, i.e. for every $T$-point $x$ of $G$ and $T$-point $n$ of $N$ there is a $T$-point $n'$ of $N$ with $i \circ n' = (x \cdot_L (i \circ n)) \cdot_L x^{-1}$. Write $s = \mathrm{pr}_2 : N \times_k G \to G$ and let $L.\mathrm{action}\ i : N \times_k G \to G$ be the point $(n,x) \mapsto (i \circ n) \cdot_L x$. Then there exist a scheme $Q$, a morphism $f_Q : Q \to \operatorname{Spec} k$, a morphism $q : G \to Q$ and a proof $w$ that $s$ followed by $q$ equals $L.\mathrm{action}\ i$ followed by $q$, such that $q$ followed by $f_Q$ is $f$, $f_Q$ is separated and quasi-compact, $q$ is flat, locally of finite presentation and surjective, the square formed by $s$, $L.\mathrm{action}\ i$ and the two copies of $q$ is a pullback square, and the cofork determined by $q$ and $w$ is a colimit, i.e. $q$ is the coequaliser of the two morphisms $N \times_k G \rightrightarrows G$ in schemes. The conclusion does not record quasi-compactness of $q$, nor any statement about the relative dimension of $f_Q$.
--
--   This is the existence half of the quotient theorem for a smooth group scheme by a smooth closed normal subgroup over an algebraically closed field (SGA 3, Exposé VI$_A$, 3.2), stated in the form of an effective flat epimorphism which is simultaneously a coequaliser. It is used to construct the quotient together with its own relative group law and its smoothness and relative dimension $g - h$, in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_fppf_quotient_isPullback_action_of_isClosedImmersion.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (hnormal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
      (n : SchemeHomOver t (i ≫ f)), ∃ n' : SchemeHomOver t (i ≫ f),
        NeronModelInfra.schemeHomOverComp n' (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (L.mul t x (NeronModelInfra.schemeHomOverComp n (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
            (L.inv t x)) :
    ∃ (Q : Scheme.{u}) (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q)
      (w : CategoryTheory.Limits.pullback.snd (i ≫ f) f ≫ q = L.action i ≫ q),
      q ≫ fQ = f ∧ IsSeparated fQ ∧ QuasiCompact fQ ∧
      Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
      IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q ∧
      Nonempty (IsColimit (Cofork.ofπ q w)) := by sorry
