-- Prove2me | Theorems.Thm_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
-- name    : HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/3cb7763e-3d18-577b-849d-8ccddb5687f8
-- title:
--   Étale part of a finite flat commutative group scheme over ℤₚ
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $p$ a prime such that the image of $p$ in $\mathcal{O}$ is a non-zero-divisor, with $\mathcal{O}$ carrying an algebra structure over $\mathbb{Z}/p$ whose structure map has kernel exactly the ideal $(p)$, and with $\mathcal{O}$ complete and separated for the $(p)$-adic topology. Let $L$ be a commutative ring which is a Hopf $\mathcal{O}$-algebra with cocommutative comultiplication, finite and free as an $\mathcal{O}$-module. The assertion is the existence of a type $H$ equipped with a commutative ring structure, a Hopf $\mathcal{O}$-algebra structure with cocommutative comultiplication, finiteness and freeness as an $\mathcal{O}$-module and formal étaleness over $\mathcal{O}$, together with a morphism $j \colon H \to L$ of $\mathcal{O}$-bialgebras such that: $j$ is injective; the base change $\mathbb{Z}/p \otimes_{\mathcal{O}} H$ is a reduced ring; the map $\mathbb{Z}/p \otimes_{\mathcal{O}} H \to \mathbb{Z}/p \otimes_{\mathcal{O}} L$ induced by $j$, followed by the quotient by the nilradical of $\mathbb{Z}/p \otimes_{\mathcal{O}} L$, is bijective; and every idempotent element of $L$ lies in the range of $j$.
--
--   The hypotheses on $\mathcal{O}$ force it to be a complete discrete valuation ring with uniformiser $p$ and residue field $\mathbb{F}_p$, so this is the construction of the maximal étale quotient $G^{\mathrm{ét}}$ of a finite flat commutative group scheme $G = \operatorname{Spec} L$ over such a base, presented on coordinate rings: $H = \mathcal{O}(G^{\mathrm{ét}})$, pinned down by the fact that over the perfect residue field the étale quotient is the reduced quotient. It feeds the refinement recording faithful flatness of $j$ and the behaviour of the augmentation ideal, which is what the connected–étale analysis of finite flat group schemes uses downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_formallyEtale_bialgHom_injective_bijective_baseChange_zmodp
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (L : Type v) [CommRing L] [HopfAlgebra 𝓞 L] [Coalgebra.IsCocomm 𝓞 L]
    [Module.Free 𝓞 L] [Module.Finite 𝓞 L] :
    ∃ (H : Type v) (_ : CommRing H) (_ : HopfAlgebra 𝓞 H) (_ : Coalgebra.IsCocomm 𝓞 H)
      (_ : Module.Free 𝓞 H) (_ : Module.Finite 𝓞 H) (_ : Algebra.FormallyEtale 𝓞 H) (j : H →ₐc[𝓞] L),
      Function.Injective j ∧
      IsReduced (ZMod p ⊗[𝓞] H) ∧
      Function.Bijective ((Ideal.Quotient.mkₐ (ZMod p) (nilradical (ZMod p ⊗[𝓞] L))).comp
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (j : H →ₐ[𝓞] L))) ∧
      ∀ e : L, IsIdempotentElem e → e ∈ Set.range j := by sorry
