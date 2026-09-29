-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ec7368c6-dfbb-5434-a7af-d772993014e6
-- title:
--   Index q^{min(s,m)} of a twisted lattice over mathcal O_w
-- statement:
--   Let $K \subseteq L$ be number fields with $L$ an algebra over $K$, let $v$ be a height one prime of $\mathcal O_K$ and let $w$ be an extension of $v$ to $\mathcal O_L$, that is, a height one prime of $\mathcal O_L$ whose prime of $\mathcal O_K$ below it is $v$; write $q =$ `Ideal.absNorm v.asIdeal`, $K_v$ and $L_w$ for the $v$- and $w$-adic completions, and $\mathcal O_w$ for the valuation ring of $L_w$. Assume the ramification index of $w$ over the prime of $\mathcal O_K$ beneath it is $1$, that the local degree $f = [L_w : K_v]$ is prime, and that $\theta$ is a $K_v$-algebra automorphism of $L_w$ with $\operatorname{ord}(\theta) = f$ for which some $y \in L_w$ satisfies $\|y\| \le 1$ and $\|\theta y - y\| = 1$. Let $c \in L_w$ and $n \in K_v$ with $\|n\| = 1$, $\|1 - n\| = q^{-m}$ for a natural number $m$, and $\prod_{i<f} \theta^i(c) = n$ in $L_w$. Let $\varpi \in K_v$ with $\|\varpi\| = q^{-1}$, and let $s$ be a natural number. Then the relative index of the additive subgroup $\mathcal O_w$ in $\Lambda_s = \{y \in L_w : \theta(y) - cy \in \mathcal O_w \text{ and } \varpi^s y \in \mathcal O_w\}$, i.e. the index of $\mathcal O_w \cap \Lambda_s$ in $\Lambda_s$, equals $q^{\min(s,m)}$.
--
--   This is the local index computation occurring in Langlands' treatment of base change for $\mathrm{GL}(2)$, in the form of a count of cosets of $\mathcal O_w$ in a lattice cut out by the twisted operator $y \mapsto \theta(y) - cy$ together with a bound on denominators. It is used in the automorphic part of the argument, in the evaluation of twisted orbital-type integrals and of Hecke operators on twisted conjugacy classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
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
