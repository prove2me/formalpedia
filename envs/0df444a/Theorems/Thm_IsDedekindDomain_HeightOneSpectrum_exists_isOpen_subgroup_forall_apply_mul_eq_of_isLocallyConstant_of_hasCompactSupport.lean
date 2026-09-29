-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/3b98bab4-d9b4-5de8-ac94-590bb11a01e2
-- title:
--   Open unit subgroup fixing a locally constant compactly supported Φ
-- statement:
--   Let $K$ be a number field and $v$ a height one prime of its ring of integers $\mathcal O_K$, with $K_v$ the associated adic completion. Let $\Phi : K_v \times K_v \to \mathbb C$ be a function which is locally constant (in the sense of `IsLocallyConstant`, i.e. the preimage of every set is open) and has compact support (the closure of $\{p : \Phi(p) \neq 0\}$ is compact), and suppose further that $\Phi(p) \neq 0$ implies that both coordinates $p_1$ and $p_2$ are nonzero. The assertion is that there exists a subgroup $U$ of the unit group $K_v^\times$ whose underlying set is open in $K_v^\times$ such that for every $t \in U$ and all $b, z \in K_v$ one has $\Phi(b t, z) = \Phi(b, z)$, where $t$ is viewed in $K_v$ through the coercion from units. Thus $\Phi$ is invariant under multiplication of its first argument by an open subgroup of units, uniformly in both arguments, not merely on the support.
--
--   This is the standard smoothness statement that a locally constant compactly supported function on a locally profinite group is fixed by an open compact subgroup, here in the multiplicative form needed for the first variable of a function of two $v$-adic variables. It is used in the construction and evaluation of local windows for hyperbolic class sums and orbital integrals, where an explicit level of invariance in the multiplicative variable is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_isOpen_subgroup_forall_apply_mul_eq_of_isLocallyConstant_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (Φ : (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) (hΦ0 : ∀ p, Φ p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∃ U : Subgroup (v.adicCompletion K)ˣ, IsOpen (U : Set (v.adicCompletion K)ˣ) ∧
      ∀ t ∈ U, ∀ b z : v.adicCompletion K, Φ (b * (t : v.adicCompletion K), z) = Φ (b, z) := by sorry
