-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel
-- name    : LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/84a15d9d-ee64-510e-a39c-b70d384bb140
-- title:
--   The level of an additive character of Kᵥ is attained
-- statement:
--   Let $K$ be a number field, $v$ a height-one prime of the ring of integers $\mathcal{O}_K$ (a finite place), and $K_v =$ `v.adicCompletion K` the associated completion, carrying its valuation $|\cdot|_v$ (`Valued.v`) with values in $\{0\}\cup\exp(\mathbb{Z})$. Let $\psi$ be an additive character of $K_v$ with values in $\mathbb{C}$ (a monoid homomorphism from the additive group of $K_v$ to $\mathbb{C}$). Assume: (i) $\psi$ is trivial on some ball, i.e. there exists $k\in\mathbb{Z}$ such that $\psi(x)=1$ for all $x$ with $|x|_v\le\exp k$; and (ii) $\psi\neq 1$. Write $n = \operatorname{addCharLevel}\psi$, defined as the supremum in $\mathbb{Z}$ of the set $S=\{k\in\mathbb{Z} : \psi(x)=1 \text{ whenever } |x|_v\le\exp k\}$. The conclusion is the conjunction of two assertions: first, $n\in S$, that is $\psi(x)=1$ for every $x\in K_v$ with $|x|_v\le\exp n$; second, $n+1\notin S$, witnessed explicitly: there exists $x\in K_v$ with $|x|_v\le\exp(n+1)$ and $\psi(x)\neq 1$. Thus the supremum defining the level is a maximum, and it is sharp.
--
--   This is the standard fact that a non-trivial additive character of a non-archimedean local field which is trivial on some ball has a well-defined largest such ball, the level (or conductor exponent) of the character; it turns `addCharLevel`, defined as a supremum of integers, into an exact invariant. It underlies the normalisation of local additive characters, Haar measures and local constants used in the Rankin–Selberg and automorphic-form estimates that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_forall_eq_one_and_exists_ne_one_of_addCharLevel.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.forall_eq_one_and_exists_ne_one_of_addCharLevel (K : Type) [Field K]
    [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψk : ∃ k : ℤ, ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp k → ψ x = 1) (hψ : ψ ≠ 1) :
    (∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ) → ψ x = 1) ∧
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (addCharLevel ψ + 1) ∧ ψ x ≠ 1 := by sorry
