-- Prove2me | Theorems.Thm_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
-- name    : Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/6b697c45-cd47-568b-a8a0-32d2f060cf22
-- title:
--   Dimension bound for the 𝔪-annihilator of a commuting family
-- statement:
--   Let $K$ be a field of characteristic $p$ for a prime $p$, let $V$ be a $K$-vector space, and let $F$ be a commuting family indexed by $\sigma$, i.e. a map $a \mapsto F.T\,a$ from $\sigma$ to $\operatorname{End}_K(V)$ whose members pairwise commute. Let $k_0$ be a finite field that is an algebra over $\mathbb{Z}/p$, let $\theta_0 \colon \sigma \to k_0$ be a map whose range generates $k_0$ as a $\mathbb{Z}/p$-algebra ($\operatorname{Algebra.adjoin}_{\mathbb{Z}/p}(\operatorname{range}\theta_0) = \top$), and let $e \colon k_0 \to K$ be a ring homomorphism. Let $W \le V$ be a $K$-subspace with $F.T\,a\,v \in W$ for all $a \in \sigma$ and $v \in W$, and let $d \in \mathbb{N}$ be such that for every ring homomorphism $\tau \colon k_0 \to K$ the subspace $W \cap \bigcap_{a \in \sigma} \ker\bigl(F.T\,a - \tau(\theta_0 a)\cdot \mathrm{id}\bigr)$ is finite-dimensional over $K$ of dimension at most $d$. Then $W \cap F.\mathrm{annPart}\,p\,(e \circ \theta_0)$, that is the intersection of $W$ with $\bigcap \ker\bigl(F.\mathrm{eval}(Q^K)\bigr)$ taken over all $Q \in (\mathbb{Z}/p)[X_a : a \in \sigma]$ whose image $Q^K$ under the coefficientwise map to $K$ satisfies $Q^K(e \circ \theta_0) = 0$, where $F.\mathrm{eval}$ evaluates a polynomial at the family $(F.T\,a)_a$ inside $\operatorname{End}_K(V)$, is finite-dimensional over $K$, of dimension at most $\dim_{\mathbb{Z}/p}(k_0) \cdot d$.
--
--   This is the linear-algebra step converting a bound on joint eigenspaces for each embedding of a residue field $k_0$ into $K$ into a bound on the annihilator of the corresponding maximal ideal of $(\mathbb{Z}/p)[X_a : a \in \sigma]$ acting through the commuting operators; only the inequality is asserted, not the splitting into eigenspaces that underlies it. It is used in [`ModularCurve.finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top`](thm.html#ModularCurve.finrank_mTorsionDiffOf_le_finrank_of_adjoin_range_eq_top), where the operators are Hecke operators and $\mathfrak m$-torsion is compared with Hecke eigenspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_CommFamily_finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le.lean

import Mathlib
import Definitions.Def_Module_CommFamilyAnnPart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem Module.End.CommFamily.finrank_inf_annPart_le_finrank_mul_of_forall_finrank_inf_iInf_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : Type*}
    (F : Module.End.CommFamily K V σ) (p : ℕ) [Fact p.Prime] [CharP K p]
    {k₀ : Type*} [Field k₀] [Finite k₀] [Algebra (ZMod p) k₀]
    (θ₀ : σ → k₀) (hgen : Algebra.adjoin (ZMod p) (Set.range θ₀) = ⊤) (e : k₀ →+* K)
    (W : Submodule K V) (hW : ∀ (a : σ) (v : V), v ∈ W → F.T a v ∈ W) (d : ℕ)
    (hd : ∀ τ : k₀ →+* K,
      FiniteDimensional K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ∧
        Module.finrank K ↥(W ⊓ ⨅ a : σ, LinearMap.ker (F.T a - τ (θ₀ a) • LinearMap.id)) ≤ d) :
    FiniteDimensional K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ∧
      Module.finrank K ↥(W ⊓ F.annPart p (e ∘ θ₀)) ≤ Module.finrank (ZMod p) k₀ * d := by sorry
