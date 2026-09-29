-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent
-- name    : HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/1194eeba-e74e-5898-9a8a-e6f539b1c0ca
-- title:
--   Finite-part quotient Hopf algebra H/(1-e) over a local ring
-- statement:
--   Let $R$ be a commutative local ring, $H$ a commutative ring carrying the structure of a Hopf $R$-algebra, and $e \in H$ an idempotent element ($e^2 = e$). Assume the localisation $\mathrm{Localization.Away}\ e = H[1/e]$ is a finite $R$-module, and that the maximal ideal of $R$ generates the unit ideal of $\mathrm{Localization.Away}\ (1-e) = H[1/(1-e)]$, i.e. its image ideal under the structure map $R \to H[1/(1-e)]$ is $\top$. Then there exist a type $H^{\mathrm f}$, a commutative ring structure on it, a Hopf $R$-algebra structure on it, and an $R$-bialgebra homomorphism $\pi^{\mathrm f} \colon H \to H^{\mathrm f}$ such that: $\pi^{\mathrm f}$ is surjective; the kernel of the underlying $R$-algebra map is the ideal $(1-e)$ of $H$; if the comultiplication of $H$ is cocommutative then so is that of $H^{\mathrm f}$; $H^{\mathrm f}$ is a finite $R$-module; if $H$ is flat over $R$ then so is $H^{\mathrm f}$; and $\pi^{\mathrm f}$ has the universal property that for every commutative $R$-algebra $T$ and every $R$-algebra map $\varphi \colon H \to T$ with $\varphi(e) = 1$ there is a unique $R$-algebra map $\varphi' \colon H^{\mathrm f} \to T$ with $\varphi' \circ \pi^{\mathrm f} = \varphi$.
--
--   This is the construction of the finite part $G^{\mathrm f} = \operatorname{Spec} H^{\mathrm f}$ of the quasi-finite flat group scheme $G = \operatorname{Spec} H$ over a local base, cut out by the finite-part idempotent $e$: the quotient $H/(1-e)$ is again a Hopf algebra, finite over $R$, and represents the open-and-closed subgroup on which $e$ is invertible. It is used in the descent of faithful flatness for quotients by orbit idempotents after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_span_one_sub_of_finitePartIdempotent
    (R : Type) [CommRing R] [IsLocalRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H]
    (e : H) (he : IsIdempotentElem e) (hfin : Module.Finite R (Localization.Away e))
    (hgen : Ideal.map (algebraMap R (Localization.Away (1 - e))) (IsLocalRing.maximalIdeal R) = ⊤) :
    ∃ (Hf : Type) (_ : CommRing Hf) (_ : HopfAlgebra R Hf) (πf : H →ₐc[R] Hf),
      Function.Surjective πf ∧
      RingHom.ker (πf : H →ₐ[R] Hf) = Ideal.span {1 - e} ∧
      (Coalgebra.IsCocomm R H → Coalgebra.IsCocomm R Hf) ∧
      Module.Finite R Hf ∧
      (Module.Flat R H → Module.Flat R Hf) ∧
      (∀ (T : Type) [CommRing T] [Algebra R T] (φ : H →ₐ[R] T), φ e = 1 →
        ∃! φ' : Hf →ₐ[R] T, φ'.comp (πf : H →ₐ[R] Hf) = φ) := by sorry
