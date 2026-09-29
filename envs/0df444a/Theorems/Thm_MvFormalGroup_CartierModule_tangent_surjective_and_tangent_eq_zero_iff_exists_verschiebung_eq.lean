-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
-- name    : MvFormalGroup.CartierModule.tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/93f647ff-4296-599b-a47e-16027212ae5e
-- title:
--   Cartier's tangent map: surjectivity and kernel VM
-- statement:
--   Let $p$ be a prime, let $R$ be a commutative ring with $\mathrm{char}\,R = p$, let $d$ be a natural number, and let $\Phi$ be a $d$-dimensional formal group law over $R$, i.e. a $d$-tuple $\Phi_1,\dots,\Phi_d$ of power series in the variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant terms, linear part $X_i + Y_i$, and satisfying the associativity identity, assumed moreover commutative in the sense that interchanging the two blocks of variables fixes each $\Phi_i$. Let $M =$ [`MvFormalGroup.CartierModule p Φ`](def/MvFormalGroup_CartierModule.html#L162) be the group of $d$-tuples $f$ of power series in variables indexed by $\mathbb{N}$, each with vanishing constant term, satisfying $f_j(S_0,S_1,\dots) = \Phi_j\bigl(f(X_{0,\bullet}),f(X_{1,\bullet})\bigr)$ for all $j$, where $S_n$ is the image in $R$ of the $n$-th Witt addition polynomial; let $\tau =$ `tangent` $\colon M \to (\mathrm{Fin}\,d \to R)$ be the additive map taking $f$ to the tuple of coefficients of the first variable $X_0$ in the $f_j$, and let $V =$ `verschiebung` be the additive endomorphism of $M$ given by `precomp` along `WittLaw.frobFam`, which `WittLaw.isEndo_frobFam` certifies to be an endomorphism of the Witt addition law. The theorem asserts the conjunction: $\tau$ is surjective, and for every $f \in M$ one has $\tau(f) = 0$ if and only if $f = V g$ for some $g \in M$.
--
--   This is the first structure theorem of Cartier theory for formal group laws in characteristic $p$: the tangent map on the module of $p$-typical curves is onto the Lie algebra $R^d$ with kernel exactly $VM$, so that $\tau$ induces an isomorphism $M/VM \cong R^d$. It is used in the study of formal $\mathcal{O}_D$-modules, where the Lie quotient $M/VM$ is identified with the target of the tangent map and the speciality condition is read off on it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
        (MvFormalGroup.CartierModule.tangent :
          MvFormalGroup.CartierModule p Φ → Fin d → R) ∧
      ∀ f : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.tangent f = 0 ↔
          ∃ g : MvFormalGroup.CartierModule p Φ,
            MvFormalGroup.CartierModule.verschiebung g = f := by sorry
