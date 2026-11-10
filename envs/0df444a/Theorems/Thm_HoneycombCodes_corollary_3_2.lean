-- Prove2me | Theorems.Thm_HoneycombCodes_corollary_3_2
-- name    : HoneycombCodes.corollary_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:20.106204+00:00
-- url     : https://prove2.me/theorems/d592ee17-72bf-4d5d-81bd-786a32d9a48e
-- title:
--   Corollary 3.2 — Perron-vector form of the moving-projection bound
-- statement:
--   In the setting of Theorem 3.1, assume that the retained positive-weight graph is connected. Let $v$ be the positive unit Perron vector of $J_\Omega=(\sqrt{p_{\omega,\omega'}p_{\omega',\omega}})$ and $\Lambda_\Omega=\lambda_{max}(J_\Omega)$. If $\Lambda_\Omega>\max\{s,0\}$, then every $C\subseteq X$ with $t(x,y)\le s$ for distinct $x,y\in C$ satisfies
--
--   $$
--   |C|\le\frac{1-s}{d_E(\Lambda_\Omega-s)}\Bigl(\sum_{\omega\in\Omega}\sqrt{D_\omega}\,v_\omega\Bigr)^2\le\frac{1-s}{d_E(\Lambda_\Omega-s)}\sum_{\omega\in\Omega}D_\omega, \tag{21}
--   $$
--
--   and the second inequality is strict unless $v$ is proportional to $(\sqrt{D_\omega})_{\omega\in\Omega}$.
--
--   This is the form of the bound used for the dimension-sum specialization (40) of Theorem 4.8.
--
--   Differences from the source:
--
--   - encoding: fibers E_x of the homogeneous bundle and ϕ_{ω,x}[g,u] = gϕ_{ω,o}u; C*(ℓ_x ⊗ ϕ_{ω,x}u) = c ϕ_{ω′,x}u (15) → (15) for every g ∈ G and u ∈ E with x = g·o, in the adjoint-free form ⟪C v′, ℓ_{g·o} ⊗ ρ_ω(g)ϕ_ω u⟫ = c ⟪v′, ρ_{ω′}(g)ϕ_{ω′} u⟫ for all v′; reason: the bundle maps are determined by ϕ_{ω,o}, and the inner-product identity for all v′ is equivalent to the adjoint identity
--   - encoding: dim Hom_H(E, Res V_ω) = 1 → a nonzero H-intertwiner E → V_ω exists and every H-intertwiner is a complex multiple of it; reason: the same condition stated without a module structure on the intertwiner space
--   - encoding: the scalars c_{ω,ω′} produced by multiplicity one, with phases chosen so that c ≥ 0 → intertwiners C and scalars c ≥ 0 taken as data, with (15) as a hypothesis; reason: the paper's choice satisfies the hypotheses; the statement holds for every such choice
--   - generalization: retained edges: exactly the pairs with V_{ω′} occurring in W ⊗ V_ω (p_{ω,ω′} = 0 on missing edges) → an arbitrary relation `retained`, with isometric intertwiners and (15) required only on retained pairs and p = 0 off them; reason: the paper's retained set is one such relation, so the Lean statement specializes to the source's
--   - encoding: the positive unit Perron vector v of J_Ω → any v with positive entries, Σ v_ω² = 1 and J_Ω v = λ_max(J_Ω) v, with λ_max the published BlockBochner.lamMax; reason: for a connected nonnegative symmetric matrix this vector is unique, so the two quantifications agree
--   - reading: the second inequality is strict unless v is proportional to (√D_ω) → if no real r has v = r·(√D_ω)_ω, the second inequality is strict; reason: literal reading of 'strict unless'
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §3, Corollary 3.2, eq. (21), p.16 (PDF 18)

import Mathlib
import Definitions.Def_HoneycombCodes_IsMPSetup
import Definitions.Def_HoneycombCodes_lamProfile
import Definitions.Def_BlockBochner_lamMax

set_option autoImplicit false

open scoped InnerProductSpace TensorProduct

namespace HoneycombCodes

/-- **Corollary 3.2**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.16 (PDF 18). In the setting of Theorem 3.1, assume the retained
positive-weight graph is connected, let `v` be the positive unit Perron vector of
`J_Ω = (√(p_{ω,ω′} p_{ω′,ω}))` and `Λ_Ω = λ_max(J_Ω)`. If `Λ_Ω > max{s, 0}`, then every
`C ⊆ X` with `t(x, y) ≤ s` off the diagonal satisfies
`|C| ≤ (1 − s)/(d_E(Λ_Ω − s)) (Σ_ω √D_ω v_ω)² ≤ (1 − s)/(d_E(Λ_Ω − s)) Σ_ω D_ω` (21), and the
second inequality is strict unless `v` is proportional to `(√D_ω)_ω`.

**Formalization Note.** "The positive unit Perron vector" is any `v` with positive entries,
`Σ v_ω² = 1` and `J_Ω v = Λ_Ω v` (for a connected nonnegative symmetric matrix this vector is
unique). `λ_max` is `BlockBochner.lamMax` (the published largest-eigenvalue definition); connectivity is that of `posWeightGraph`. `[DecidableEq Ω]` is needed only to form the
spectrum of a matrix indexed by `Ω`. "Strict unless
proportional" is: if no real `r` has `v = r (√D_ω)_ω`, the second inequality is strict. -/
theorem corollary_3_2
    {G : Type*} [Group G] [Fintype G] {X : Type*} [Fintype X] [MulAction G X] (o : X)
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (ρW : Representation ℂ G W) (ℓ : X → W)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (ρE : Representation ℂ (MulAction.stabilizer G o) E)
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (V : Ω → Type*) [∀ ω, NormedAddCommGroup (V ω)]
    [∀ ω, InnerProductSpace ℂ (V ω)] [∀ ω, FiniteDimensional ℂ (V ω)]
    (ρ : ∀ ω, Representation ℂ G (V ω)) (ϕ : ∀ ω, E →ₗ[ℂ] V ω)
    (retained : Ω → Ω → Prop) (C : ∀ ω ω', V ω' →ₗ[ℂ] (W ⊗[ℂ] V ω)) (c : Ω → Ω → ℝ)
    (hsetup : IsMPSetup o ρW ℓ ρE V ρ ϕ retained C c)
    (hconn : (posWeightGraph (pcoef retained c)).Connected)
    (s : ℝ) (v : Ω → ℝ) (hvpos : ∀ ω, 0 < v ω) (hvunit : ∑ ω, v ω ^ 2 = 1)
    (hvperron : (symJ (pcoef retained c)).mulVec v = BlockBochner.lamMax (symJ (pcoef retained c)) • v)
    (hΛ : max s 0 < BlockBochner.lamMax (symJ (pcoef retained c)))
    (Cset : Finset X) (hC : ∀ x ∈ Cset, ∀ y ∈ Cset, x ≠ y → (⟪ℓ x, ℓ y⟫_ℂ).re ≤ s) :
    let K : ℝ := (1 - s) /
      ((Module.finrank ℂ E : ℝ) * (BlockBochner.lamMax (symJ (pcoef retained c)) - s))
    (Cset.card : ℝ) ≤ K * (∑ ω, Real.sqrt (Module.finrank ℂ (V ω) : ℝ) * v ω) ^ 2 ∧
      K * (∑ ω, Real.sqrt (Module.finrank ℂ (V ω) : ℝ) * v ω) ^ 2 ≤
        K * ∑ ω, (Module.finrank ℂ (V ω) : ℝ) ∧
      ((¬ ∃ r : ℝ, ∀ ω, v ω = r * Real.sqrt (Module.finrank ℂ (V ω) : ℝ)) →
        K * (∑ ω, Real.sqrt (Module.finrank ℂ (V ω) : ℝ) * v ω) ^ 2 <
          K * ∑ ω, (Module.finrank ℂ (V ω) : ℝ)) := by sorry

end HoneycombCodes
