-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_algEquiv_of_baseChange
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_tensor_adicCompletion_algEquiv_of_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/c85df402-1170-50bf-9eed-67aa2ac149d1
-- title:
--   Completion commutes with base change along a compositum
-- statement:
--   Let $K$, $L$, $K'$, $M$ be number fields with $L$ and $K'$ algebras over $K$ and $M$ an algebra over each of $K$, $L$, $K'$, the scalar towers $K \to L \to M$ and $K \to K' \to M$ being compatible. Assume $\operatorname{finrank}_{K'} M = \operatorname{finrank}_K L$, and that every element of $M$ lies in `Algebra.adjoin K'` of the image of $L$ in $M$ (so $M$ is generated over $K'$ by $L$). Let $v$ be a height-one prime of $\mathcal{O}_K$, let $w$ be a height-one prime of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$, and let $\mathfrak{v}$ be a height-one prime of $\mathcal{O}_{K'}$ whose contraction to $\mathcal{O}_K$ is $v$; assume $\operatorname{finrank}_{K_v} L_w = \operatorname{finrank}_K L$, where $K_v$ and $L_w$ denote the adic completions. Then there exists an isomorphism of $K'_{\mathfrak{v}}$-algebras $e \colon M \otimes_{K'} K'_{\mathfrak{v}} \to K'_{\mathfrak{v}} \otimes_{K_v} L_w$, the $K'_{\mathfrak{v}}$-structures being those on the right-hand tensor factor of the source and the left-hand factor of the target, such that for all $a \in K'$, $b \in L$ and $c \in K'_{\mathfrak{v}}$ one has $e\big((a_M b_M) \otimes c\big) = (a_{K'_{\mathfrak{v}}} c) \otimes b_{L_w}$, subscripts denoting the structure maps into $M$, $K'_{\mathfrak{v}}$ and $L_w$.
--
--   This is the statement that extension of scalars commutes with completion for a compositum: under the stated degree and generation hypotheses $M$ is the base change of $L/K$ to $K'$, and the hypothesis on $[L_w : K_v]$ makes $w$ the unique place of $L$ above $v$, so the completion of $M$ at a place over $\mathfrak{v}$ is obtained from $L_w$ by base change to $K'_{\mathfrak{v}}$. It is used in the comparison of local norms and valuations at places above $v$, being cited by [`IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm`](thm.html#IsDedekindDomain.HeightOneSpectrum.exists_units_prod_tensor_map_iterate_eq_tmul_one_of_finrank_dvd_valuation_norm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_tensor_adicCompletion_algEquiv_of_baseChange.lean

import Mathlib
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem IsDedekindDomain.HeightOneSpectrum.exists_tensor_adicCompletion_algEquiv_of_baseChange
    (K L K' M : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field K'] [NumberField K']
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K K'] [Algebra K M] [Algebra L M] [Algebra K' M]
    [IsScalarTower K L M] [IsScalarTower K K' M]
    (hdisj : Module.finrank K' M = Module.finrank K L)
    (hcomp : ∀ x : M, x ∈ Algebra.adjoin K' (Set.range (algebraMap L M)))
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L)) (𝔳 : v.Extension (𝓞 K'))
    (hfin : Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = Module.finrank K L) :
    ∃ e : (M ⊗[K'] 𝔳.1.adicCompletion K') ≃ₐ[𝔳.1.adicCompletion K']
        (𝔳.1.adicCompletion K' ⊗[v.adicCompletion K] w.1.adicCompletion L),
      ∀ (a : K') (b : L) (c : 𝔳.1.adicCompletion K'),
        e ((algebraMap K' M a * algebraMap L M b) ⊗ₜ[K'] c) =
          (algebraMap K' (𝔳.1.adicCompletion K') a * c) ⊗ₜ[v.adicCompletion K]
            algebraMap L (w.1.adicCompletion L) b := by sorry
