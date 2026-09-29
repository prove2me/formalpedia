-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one
-- name    : IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/543fa9d0-41db-5bb3-a5cb-2b66409a0e39
-- title:
--   Unramified non-trivial automorphism moves an integer by a unit
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a Galois extension of $K$, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $w$ be an extension of $v$ to $L$, i.e. a height-one prime of $\mathcal{O}_L$ together with the requirement that its contraction to $\mathcal{O}_K$ is $v$. Assume that the ramification index $e$ of the prime $w$ over its contraction to $\mathcal{O}_K$ is equal to $1$. Let $\theta$ be an automorphism of the $w$-adic completion $L_w$ as an algebra over the $v$-adic completion $K_v$, and assume $\theta \neq 1$. Then there exists $y \in L_w$ with $\|y\| \le 1$ and $\|\theta(y) - y\| = 1$, the norm being the normalised absolute value attached to the finite place $w$. Equivalently, $y$ lies in the valuation ring of $L_w$ and $\theta(y) - y$ is a unit of that ring.
--
--   This is the statement that at an unramified place the reduction map from $\mathrm{Gal}(L_w/K_v)$ to the residue-field automorphisms is injective, in the concrete form used for estimates: a non-trivial $K_v$-automorphism of $L_w$ moves some integer by a unit. It is used in the bound for twisted orbital integrals of the indicator function of a semi-local integral set at places with $e = 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_Extension_exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one.lean

import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.Extension.exists_norm_le_one_and_norm_algEquiv_sub_eq_one_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) (hθ : θ ≠ 1) :
    ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1 := by sorry
