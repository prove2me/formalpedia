-- Prove2me | Theorems.Thm_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
-- name    : HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/b17ab6de-267d-5af0-8d1f-1d713b7ef37d
-- title:
--   Connected components of a finite flat group scheme as G⁰-torsors
-- statement:
--   Let $R$ be a commutative local ring whose residue field is algebraically closed, and let $H$ be a commutative Hopf algebra over $R$ that is finite and flat as an $R$-module. Let $\iota$ be a finite index type and $e : \iota \to H$ a complete family of orthogonal idempotents (pairwise orthogonal idempotents summing to $1$), and assume that each quotient ring $H_i := H/(1-e_i)$ is local; fix $i_0 \in \iota$ with $\varepsilon(e_{i_0}) = 1$, where $\varepsilon$ is the counit. Write $q_i : H \to H_i$ for the quotient $R$-algebra maps and $\Delta =$ `Bialgebra.comulAlgHom R H`. The assertion is that for every $i \in \iota$: $H_i$ is free and faithfully flat as an $R$-module, $\operatorname{rank}_R H_i = \operatorname{rank}_R H_{i_0}$, and there is an $R$-algebra homomorphism $\rho : H_i \to H_i \otimes_R H_{i_0}$ with $\rho \circ q_i = (q_i \otimes q_{i_0}) \circ \Delta$, such that the $R$-algebra map $H_i \otimes_R H_i \to H_i \otimes_R H_{i_0}$ determined by $a \otimes b \mapsto (a \otimes 1)\rho(b)$ is bijective, and such that for every commutative $R$-algebra $L$ and all $R$-algebra maps $t : H_i \to L$, $w : H_{i_0} \to L$, the composite of $q_i$, $\rho$ and the multiplication-lift of $t$ and $w$ equals the convolution product of $t \circ q_i$ and $w \circ q_{i_0}$ in the convolution monoid structure (`WithConv`) on $R$-algebra maps $H \to L$.
--
--   Geometrically this is the component structure of a finite flat commutative group scheme $G = \operatorname{Spec} H$ over a local ring with algebraically closed residue field: once $G$ is split into its connected components $P_i = \operatorname{Spec} H_i$, each $P_i$ is a $G^0$-torsor trivialised over itself, via $P_i \times_R G^0 \cong P_i \times_R P_i$, $(t,w) \mapsto (t, t\cdot w)$, and all components have the same rank over $R$; the last clause records that $\rho$ implements translation by $G^0$ on points. It feeds the analysis of torsion points on the Néron extension attached to $J_0$ at $p$, via [`ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf`](thm.html#ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_isFinite_forall_ptsN_comp_eq_of_hopf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_comul_quotient_bijective_of_completeOrthogonalIdempotents_of_counit_apply_eq_one
    (R : Type) [CommRing R] [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    (ι : Type) [Fintype ι] (e : ι → H) (he : CompleteOrthogonalIdempotents e)
    (hloc : ∀ i : ι, IsLocalRing (H ⧸ Ideal.span {1 - e i}))
    (i₀ : ι) (h₀ : Coalgebra.counit (R := R) (e i₀) = 1) :
    ∀ i : ι,
      Module.Free R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.FaithfullyFlat R (H ⧸ Ideal.span {1 - e i}) ∧
      Module.finrank R (H ⧸ Ideal.span {1 - e i}) = Module.finrank R (H ⧸ Ideal.span {1 - e i₀}) ∧
      ∃ ρ : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}),
        ρ.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
          (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀}))).comp
            (Bialgebra.comulAlgHom R H) ∧
        Function.Bijective
          (Algebra.TensorProduct.lift
            (Algebra.TensorProduct.includeLeft :
              (H ⧸ Ideal.span {1 - e i}) →ₐ[R] (H ⧸ Ideal.span {1 - e i}) ⊗[R] (H ⧸ Ideal.span {1 - e i₀}))
            ρ (fun _ _ => Commute.all _ _)) ∧
        ∀ (L : Type) [CommRing L] [Algebra R L]
          (t : (H ⧸ Ideal.span {1 - e i}) →ₐ[R] L) (w : (H ⧸ Ideal.span {1 - e i₀}) →ₐ[R] L),
          ((Algebra.TensorProduct.lift t w (fun _ _ => Commute.all _ _)).comp ρ).comp
              (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i})) =
            (WithConv.toConv (t.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i}))) *
              WithConv.toConv (w.comp (Ideal.Quotient.mkₐ R (Ideal.span {1 - e i₀})))).ofConv := by sorry
