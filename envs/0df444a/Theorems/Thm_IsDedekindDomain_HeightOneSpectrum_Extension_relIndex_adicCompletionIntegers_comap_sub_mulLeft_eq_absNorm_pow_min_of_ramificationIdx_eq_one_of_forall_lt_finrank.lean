-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/910705e7-348a-519b-89c2-4d9e9541eb3e
-- title:
--   Index of a twisted lattice at an unramified place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal{O}_K$ and let $w$ be a nonzero prime of $\mathcal{O}_L$ lying under $v$ (an element of `v.Extension (𝓞 L)`, i.e. a height-one prime of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$); write $q =$ `Ideal.absNorm v.asIdeal` and $f = [L_w : K_v]$ for the degree of the completion $L_w$ over $K_v$. Assume the ramification index of $w$ over the prime under it equals $1$. Let $\theta$ be a $K_v$-algebra automorphism of $L_w$ whose order is exactly $f$, such that for every $j$ with $0 < j < f$ there is $y \in L_w$ with $\|y\| \le 1$ and $\|\theta^j(y) - y\| = 1$. Let $c \in L_w$ and $n \in K_v$ with $\|n\| = 1$, let $m \in \mathbb{N}$ satisfy $\|1 - n\| = q^{-m}$, and suppose $\prod_{i<f} \theta^i(c) = n$ in $L_w$. Let $\varpi \in K_v$ have $\|\varpi\| = q^{-1}$ and let $s \in \mathbb{N}$. Then the additive subgroup $\mathcal{O}_{L_w}$ has relative index $q^{\min(s,m)}$ in the intersection of $\{y : \theta(y) - cy \in \mathcal{O}_{L_w}\}$ with the preimage of $\mathcal{O}_{L_w}$ under multiplication by $\varpi^s$, that is, the index of $\mathcal{O}_{L_w}$ intersected with that intersection inside it is $q^{\min(s,m)}$.
--
--   This is the local lattice count underlying the evaluation of twisted orbital integrals of spherical functions at an unramified place in cyclic base change: after an Iwasawa decomposition the twisted orbit of a diagonal element meets the maximal compact subgroup along the unipotent image of the twisted lattice $\{y : \theta(y) - cy \in \mathcal{O}_{L_w}\}$. It is used in the computation of the twisted orbital integral of the indicator function of a semi-local integral set at a place with ramification index one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∀ j : ℕ, 0 < j → j < Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) →
      ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖(θ ^ j) y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
        (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
          ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
            (AddMonoidHom.mulLeft
              (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
      Ideal.absNorm v.asIdeal ^ min s m := by sorry
